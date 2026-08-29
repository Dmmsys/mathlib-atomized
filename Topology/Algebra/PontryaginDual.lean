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

/--
Definition of `PontryaginDual` / `PontryaginDual` 的定义

English:
definition PontryaginDual
  body: A ->ₜ* Circle
deriving TopologicalSpace

中文:
定义 PontryaginDual
  定义体: A ->ₜ* Circle
deriving TopologicalSpace

Depends on / 依赖: Circle
-/
def PontryaginDual :=
  A ->ₜ* Circle
deriving TopologicalSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallyCompactSpace
  signature: H] : LocallyCompactSpace (PontryaginDual H)
  body: by
  let Vn : Nat -> Set Circle := fun n => Circle.centeredArc (π / 2 ^ (n + 1))
  have hVn : forall n x, x in Vn n ↔ |Complex.arg x| < π / 2 ^ (n + 1) :=
    fun n x => Circle.mem_centeredArc (z := x)
      (div_le_self pi_nonneg (one_le_pow₀ one_le_two))
  refine ContinuousMonoidHom.locallyCompact

中文:
实例 [LocallyCompactSpace
  签名: H] : LocallyCompactSpace (PontryaginDual H)
  定义体: by
  let Vn : Nat -> Set Circle := fun n => Circle.centeredArc (π / 2 ^ (n + 1))
  have hVn : forall n x, x in Vn n ↔ |Complex.arg x| < π / 2 ^ (n + 1) :=
    fun n x => Circle.mem_centeredArc (z := x)
      (div_le_self pi_nonneg (one_le_pow₀ one_le_two))
  refine ContinuousMonoidHom.locallyCompact

Depends on / 依赖: Circle, Circle.centeredArc, Circle.coe_mul, Circle.mem_centeredArc, Complex.arg, Complex.arg_mul, ContinuousMonoidHom, ContinuousMonoidHom.locallyCompactSpace_of_hasBasis, abs_mul, abs_two, arg_mul, centeredArc, coe_mul, coe_ne_zero, div_div, div_le_self, locallyCompactSpace_of_hasBasis, mem_centeredArc, one_le_two, pi_nonneg
-/
instance [LocallyCompactSpace H] : LocallyCompactSpace (PontryaginDual H) := by
  let Vn : Nat -> Set Circle := fun n => Circle.centeredArc (π / 2 ^ (n + 1))
  have hVn : forall n x, x in Vn n ↔ |Complex.arg x| < π / 2 ^ (n + 1) :=
    fun n x => Circle.mem_centeredArc (z := x)
      (div_le_self pi_nonneg (one_le_pow₀ one_le_two))
  refine ContinuousMonoidHom.locallyCompactSpace_of_hasBasis Vn ?_ ?_
  · intro n x h1 h2
    rw [hVn] at h1 h2 ⊢
    rwa [Circle.coe_mul, Complex.arg_mul x.coe_ne_zero x.coe_ne_zero,
      ← two_mul, abs_mul, abs_two, ← lt_div_iff₀' two_pos, div_div, ← pow_succ] at h2
    apply Set.Ioo_subset_Ioc_self
    rw [← two_mul]; rw [Set.mem_Ioo]; rw [← abs_lt]; rw [abs_mul]; rw [abs_two]; rw [← lt_div_iff₀' two_pos]
    refine h1.trans_le ?_
    gcongr
    exact le_self_pow₀ one_le_two n.succ_ne_zero
  · simpa [Vn] using Circle.hasBasis_centeredArc_div_two_pow

variable {A B C G}

namespace PontryaginDual

open ContinuousMonoidHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommGroup (PontryaginDual A)
  body: inferInstanceAs (CommGroup (A ->ₜ* Circle))

deriving instance
  T2Space, IsTopologicalGroup,
  Inhabited, FunLike, ContinuousMapClass, MonoidHomClass,
  [DiscreteTopology A] -> CompactSpace _
for PontryaginDual A

@[ext]

中文:
实例 :
  签名: CommGroup (PontryaginDual A)
  定义体: inferInstanceAs (CommGroup (A ->ₜ* Circle))

deriving instance
  T2Space, IsTopologicalGroup,
  Inhabited, FunLike, ContinuousMapClass, MonoidHomClass,
  [DiscreteTopology A] -> CompactSpace _
for PontryaginDual A

@[ext]

Depends on / 依赖: Circle, CommGroup
-/
instance : CommGroup (PontryaginDual A) := inferInstanceAs (CommGroup (A ->ₜ* Circle))

deriving instance
  T2Space, IsTopologicalGroup,
  Inhabited, FunLike, ContinuousMapClass, MonoidHomClass,
  [DiscreteTopology A] -> CompactSpace _
for PontryaginDual A

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {ψ φ : PontryaginDual A} (h : forall a, ψ a = φ a)
  statement: ψ = φ
  proof: DFunLike.ext _ _ h

@[simp]

中文:
定理 ext
  条件: {ψ φ : PontryaginDual A} (h : 对任意 a, ψ a = φ a)
  结论: ψ = φ
  证明: DFunLike.ext _ _ h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {ψ φ : PontryaginDual A} (h : forall a, ψ a = φ a) : ψ = φ :=
  DFunLike.ext _ _ h

@[simp]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (a : A)
  statement: (1 : PontryaginDual A) a = 1
  proof: rfl

中文:
定理 one_apply
  条件: (a : A)
  结论: (1 : PontryaginDual A) a = 1
  证明: rfl
-/
theorem one_apply (a : A) : (1 : PontryaginDual A) a = 1 :=
  rfl

/-- A discrete monoid has compact Pontryagin dual. -/
add_decl_doc instLocallyCompactSpacePontryaginDual

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: A] : DiscreteTopology (PontryaginDual A)
  body: by
  let V : Set (PontryaginDual A) := {ψ | Set.MapsTo ψ Set.univ (Circle.centeredArc (π / 2))}
  have hVopen : IsOpen V := by
    dsimp only [V]
    exact isOpen_induced (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ
      (Circle.isOpen_centeredArc (π / 2)))
  have hVeq : V = ({1} : Set (Po

中文:
实例 [CompactSpace
  签名: A] : DiscreteTopology (PontryaginDual A)
  定义体: by
  let V : Set (PontryaginDual A) := {ψ | Set.MapsTo ψ Set.univ (Circle.centeredArc (π / 2))}
  have hVopen : IsOpen V := by
    dsimp only [V]
    exact isOpen_induced (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ
      (Circle.isOpen_centeredArc (π / 2)))
  have hVeq : V = ({1} : Set (Po

Depends on / 依赖: Circle, Circle.centeredArc, Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two, Circle.isOpen_centeredArc, ContinuousMap, ContinuousMap.isOpen_setOfPred_mapsTo, IsOpen, MapsTo, PontryaginDual, Set.MapsTo, Set.mem_singleton_iff, Set.mem_univ, Set.univ, centeredArc, eq_one_of_forall_pow_mem_centeredArc_pi_div_two, hVopen, isCompact_univ, isOpen_centeredArc, isOpen_induced, isOpen_setOfPred_mapsTo
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
    refine ⟨fun hψ => ?_, ?_⟩
    · ext1 a
      refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n hn => ?_
      simpa using hψ (Set.mem_univ (a ^ n))
    · rintro rfl _ _
      rw [Circle.mem_centeredArc (by linarith [pi_pos])]
      simp [pi_pos]
  exact discreteTopology_of_isOpen_singleton_one (by simpa [hVeq] using hVopen)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DiscreteTopology
  signature: A] [CompactSpace A] : Finite (PontryaginDual A)
  body: finite_of_compact_of_discrete

中文:
实例 [DiscreteTopology
  签名: A] [CompactSpace A] : Finite (PontryaginDual A)
  定义体: finite_of_compact_of_discrete

Depends on / 依赖: finite_of_compact_of_discrete
-/
instance [DiscreteTopology A] [CompactSpace A] : Finite (PontryaginDual A) :=
  finite_of_compact_of_discrete

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DiscreteTopology
  signature: A] [CompactSpace A] : Fintype (PontryaginDual A)
  body: .ofFinite _

中文:
实例 [DiscreteTopology
  签名: A] [CompactSpace A] : Fintype (PontryaginDual A)
  定义体: .ofFinite _

Depends on / 依赖: ofFinite
-/
noncomputable instance [DiscreteTopology A] [CompactSpace A] : Fintype (PontryaginDual A) :=
  .ofFinite _

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : A ->ₜ* B)
  body: f.compLeft Circle

@[simp]

中文:
定义 map
  签名: (f : A ->ₜ* B)
  定义体: f.compLeft Circle

@[simp]

Depends on / 依赖: Circle, compLeft, f.compLeft
-/
def map (f : A ->ₜ* B) :
    (PontryaginDual B) ->ₜ* (PontryaginDual A) :=
  f.compLeft Circle

@[simp]
/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: (f : A ->ₜ* B) (x : PontryaginDual B) (y : A)
  proof: rfl

@[simp]

中文:
定理 map_apply
  条件: (f : A ->ₜ* B) (x : PontryaginDual B) (y : A)
  证明: rfl

@[simp]
-/
theorem map_apply (f : A ->ₜ* B) (x : PontryaginDual B) (y : A) :
    map f x y = x (f y) :=
  rfl

@[simp]
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  statement: map (1 : A ->ₜ* B) = 1
  proof: ContinuousMonoidHom.ext fun x => PontryaginDual.ext fun _y => OneHomClass.map_one x

@[simp]

中文:
定理 map_one
  结论: map (1 : A ->ₜ* B) = 1
  证明: ContinuousMonoidHom.ext fun x => PontryaginDual.ext fun _y => OneHomClass.map_one x

@[simp]

Depends on / 依赖: ContinuousMonoidHom, ContinuousMonoidHom.ext, OneHomClass, OneHomClass.map_one, PontryaginDual, PontryaginDual.ext, map_one
-/
theorem map_one : map (1 : A ->ₜ* B) = 1 :=
  ContinuousMonoidHom.ext fun x => PontryaginDual.ext fun _y => OneHomClass.map_one x

@[simp]
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (g : B ->ₜ* C) (f : A ->ₜ* B)
  proof: ContinuousMonoidHom.ext fun _x => PontryaginDual.ext fun _y => rfl

@[simp]
nonrec theorem map_mul (f g : A ->ₜ* G) : map (f * g) = map f * map g :=
  ContinuousMonoidHom.ext fun x => PontryaginDual.ext fun y => map_mul x (f y) (g y)

中文:
定理 map_comp
  条件: (g : B ->ₜ* C) (f : A ->ₜ* B)
  证明: ContinuousMonoidHom.ext fun _x => PontryaginDual.ext fun _y => rfl

@[simp]
nonrec theorem map_mul (f g : A ->ₜ* G) : map (f * g) = map f * map g :=
  ContinuousMonoidHom.ext fun x => PontryaginDual.ext fun y => map_mul x (f y) (g y)

Depends on / 依赖: ContinuousMonoidHom, ContinuousMonoidHom.ext, PontryaginDual, PontryaginDual.ext
-/
theorem map_comp (g : B ->ₜ* C) (f : A ->ₜ* B) :
    map (comp g f) = ContinuousMonoidHom.comp (map f) (map g) :=
  ContinuousMonoidHom.ext fun _x => PontryaginDual.ext fun _y => rfl

@[simp]
nonrec theorem map_mul (f g : A ->ₜ* G) : map (f * g) = map f * map g :=
  ContinuousMonoidHom.ext fun x => PontryaginDual.ext fun y => map_mul x (f y) (g y)

variable (A B C G)

/--
Definition of `mapHom` / `mapHom` 的定义

English:
definition mapHom
  signature: [LocallyCompactSpace G]
  body: map
  map_one' := map_one
  map_mul' := map_mul
  continuous_toFun := continuous_of_continuous_uncurry _ continuous_comp

中文:
定义 mapHom
  签名: [LocallyCompactSpace G]
  定义体: map
  map_one' := map_one
  map_mul' := map_mul
  continuous_toFun := continuous_of_continuous_uncurry _ continuous_comp
-/
def mapHom [LocallyCompactSpace G] :
    (A ->ₜ* G) ->ₜ* ((PontryaginDual G) ->ₜ* (PontryaginDual A)) where
  toFun := map
  map_one' := map_one
  map_mul' := map_mul
  continuous_toFun := continuous_of_continuous_uncurry _ continuous_comp

end PontryaginDual
