/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Order.SuccPred.PartialSups
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Ideal.Prod

/-!
# Noetherian rings and modules

The following are equivalent for a module M over a ring R:
1. Every increasing chain of submodules M₁ ⊆ M₂ ⊆ M₃ ⊆ ⋯ eventually stabilises.
2. Every submodule is finitely generated.

A module satisfying these equivalent conditions is said to be a *Noetherian* R-module.
A ring is a *Noetherian ring* if it is Noetherian as a module over itself.

(Note that we do not assume yet that our rings are commutative,
so perhaps this should be called "left-Noetherian".
To avoid cumbersome names once we specialize to the commutative case,
we don't make this explicit in the declaration names.)

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `IsNoetherian R M` is the proposition that `M` is a Noetherian `R`-module. It is a class,
  implemented as the predicate that all `R`-submodules of `M` are finitely generated.

## Main statements

* `isNoetherian_iff` is the theorem that an R-module M is Noetherian iff `>` is well-founded on
  `Submodule R M`.

Note that the Hilbert basis theorem, that if a commutative ring R is Noetherian then so is R[X],
is proved in `RingTheory.Polynomial`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags

Noetherian, noetherian, Noetherian ring, Noetherian module, noetherian ring, noetherian module

-/

public section

assert_not_exists Matrix

open Set Pointwise

section

variable {R S M P : Type*}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid P]
variable [Module R M] [Module S P]

open IsNoetherian

/--
theorem `isNoetherian_of_surjective` / 定理 `isNoetherian_of_surjective`

English:
theorem isNoetherian_of_surjective
  statement: {σ : R ->+* S} [RingHomSurjective σ] (f : M ->ₛₗ[σ] P)
  proof: ⟨fun s =>
have : (s.comap f).map f = s := Submodule.map_comap_eq_self hf.symm ▸ le_top
    this ▸ (IsNoetherian.noetherian _).map _⟩

中文:
定理 isNoetherian_of_surjective
  结论: {σ : R ->+* S} [RingHomSurjective σ] (f : M ->ₛₗ[σ] P)
  证明: ⟨fun s =>
have : (s.comap f).map f = s := Submodule.map_comap_eq_self hf.symm ▸ le_top
    this ▸ (IsNoetherian.noetherian _).map _⟩

Depends on / 依赖: IsNoetherian, IsNoetherian.noetherian, Submodule, Submodule.map_comap_eq_self, hf.symm, le_top, map_comap_eq_self, noetherian, s.comap
-/
theorem isNoetherian_of_surjective {σ : R ->+* S} [RingHomSurjective σ] (f : M ->ₛₗ[σ] P)
    (hf : LinearMap.range f = ⊤) [IsNoetherian R M] :
    IsNoetherian S P :=
  ⟨fun s =>
have : (s.comap f).map f = s := Submodule.map_comap_eq_self hf.symm ▸ le_top
    this ▸ (IsNoetherian.noetherian _).map _⟩

/--
Instance `isNoetherian_map` / 实例 `isNoetherian_map`

English:
instance isNoetherian_map
  signature: {σ : R ->+* S} [RingHomSurjective σ] {s : Submodule R M}
  body: isNoetherian_of_surjective (f.submoduleMap s) (by simp [LinearMap.submoduleMap])

中文:
实例 isNoetherian_map
  签名: {σ : R ->+* S} [RingHomSurjective σ] {s : 子模 R M}
  定义体: isNoetherian_of_surjective (f.submoduleMap s) (by simp [LinearMap.submoduleMap])

Depends on / 依赖: LinearMap, LinearMap.submoduleMap, f.submoduleMap, isNoetherian_of_surjective, submoduleMap
-/
instance isNoetherian_map {σ : R ->+* S} [RingHomSurjective σ] {s : Submodule R M}
    (f : M ->ₛₗ[σ] P) [IsNoetherian R s] : IsNoetherian S (Submodule.map f s) :=
  isNoetherian_of_surjective (f.submoduleMap s) (by simp [LinearMap.submoduleMap])

/--
Instance `isNoetherian_range` / 实例 `isNoetherian_range`

English:
instance isNoetherian_range
  signature: {σ : R ->+* S} [RingHomSurjective σ] (f : M ->ₛₗ[σ] P)
  body: isNoetherian_of_surjective _ f.range_rangeRestrict

中文:
实例 isNoetherian_range
  签名: {σ : R ->+* S} [RingHomSurjective σ] (f : M ->ₛₗ[σ] P)
  定义体: isNoetherian_of_surjective _ f.range_rangeRestrict

Depends on / 依赖: f.range_rangeRestrict, isNoetherian_of_surjective, range_rangeRestrict
-/
instance isNoetherian_range {σ : R ->+* S} [RingHomSurjective σ] (f : M ->ₛₗ[σ] P)
    [IsNoetherian R M] : IsNoetherian S (LinearMap.range f) :=
  isNoetherian_of_surjective _ f.range_rangeRestrict

/--
Instance `isNoetherian_quotient` / 实例 `isNoetherian_quotient`

English:
instance isNoetherian_quotient
  signature: {A M : Type*} [Ring A] [AddCommGroup M] [SMul R A] [Module R M]
  body: isNoetherian_of_surjective ((Submodule.mkQ N).restrictScalars R)
    LinearMap.range_eq_top.mpr N.mkQ_surjective

中文:
实例 isNoetherian_quotient
  签名: {A M : 类型} [环 A] [加法交换群 M] [标量乘法 R A] [模 R M]
  定义体: isNoetherian_of_surjective ((Submodule.mkQ N).restrictScalars R)
    LinearMap.range_eq_top.mpr N.mkQ_surjective

Depends on / 依赖: LinearMap, LinearMap.range_eq_top.mpr, N.mkQ_surjective, Submodule, Submodule.mkQ, isNoetherian_of_surjective, mkQ_surjective, range_eq_top, restrictScalars
-/
instance isNoetherian_quotient {A M : Type*} [Ring A] [AddCommGroup M] [SMul R A] [Module R M]
    [Module A M] [IsScalarTower R A M] (N : Submodule A M) [IsNoetherian R M] :
    IsNoetherian R (M ⧸ N) :=
isNoetherian_of_surjective ((Submodule.mkQ N).restrictScalars R)
    LinearMap.range_eq_top.mpr N.mkQ_surjective

/--
theorem `isNoetherian_of_linearEquiv` / 定理 `isNoetherian_of_linearEquiv`

English:
theorem isNoetherian_of_linearEquiv
  statement: {σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ']
  proof: isNoetherian_of_surjective f.toLinearMap f.range

中文:
定理 isNoetherian_of_linearEquiv
  结论: {σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ']
  证明: isNoetherian_of_surjective f.toLinearMap f.range

Depends on / 依赖: f.range, f.toLinearMap, isNoetherian_of_surjective, toLinearMap
-/
theorem isNoetherian_of_linearEquiv {σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ']
    [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) [IsNoetherian R M] : IsNoetherian S P :=
  isNoetherian_of_surjective f.toLinearMap f.range

/--
theorem `LinearEquiv.isNoetherian_iff` / 定理 `LinearEquiv.isNoetherian_iff`

English:
theorem LinearEquiv.isNoetherian_iff
  statement: {σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ']
  proof: ⟨fun _ => isNoetherian_of_linearEquiv f, fun _ => isNoetherian_of_linearEquiv f.symm⟩

中文:
定理 线性等价.isNoetherian_iff
  结论: {σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ']
  证明: ⟨fun _ => isNoetherian_of_linearEquiv f, fun _ => isNoetherian_of_linearEquiv f.symm⟩

Depends on / 依赖: f.symm, isNoetherian_of_linearEquiv
-/
theorem LinearEquiv.isNoetherian_iff {σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ']
    [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) : IsNoetherian R M ↔ IsNoetherian S P :=
  ⟨fun _ => isNoetherian_of_linearEquiv f, fun _ => isNoetherian_of_linearEquiv f.symm⟩

/--
theorem `isNoetherian_top_iff` / 定理 `isNoetherian_top_iff`

English:
theorem isNoetherian_top_iff
  statement: IsNoetherian R (⊤ : Submodule R M) ↔ IsNoetherian R M
  proof: Submodule.topEquiv.isNoetherian_iff

中文:
定理 isNoetherian_top_iff
  结论: 是Noether R (⊤ : 子模 R M) ↔ 是Noether R M
  证明: Submodule.topEquiv.isNoetherian_iff

Depends on / 依赖: Submodule, Submodule.topEquiv.isNoetherian_iff, isNoetherian_iff, topEquiv
-/
theorem isNoetherian_top_iff : IsNoetherian R (⊤ : Submodule R M) ↔ IsNoetherian R M :=
  Submodule.topEquiv.isNoetherian_iff

/--
theorem `isNoetherian_of_injective` / 定理 `isNoetherian_of_injective`

English:
theorem isNoetherian_of_injective
  statement: [IsNoetherian S P] {σ : R ->+* S} {σ' : S ->+* R}
  proof: isNoetherian_of_linearEquiv (LinearEquiv.ofInjective f hf).symm

中文:
定理 isNoetherian_of_injective
  结论: [是Noether S P] {σ : R ->+* S} {σ' : S ->+* R}
  证明: isNoetherian_of_linearEquiv (LinearEquiv.ofInjective f hf).symm

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInjective, isNoetherian_of_linearEquiv, ofInjective
-/
theorem isNoetherian_of_injective [IsNoetherian S P] {σ : R ->+* S} {σ' : S ->+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ->ₛₗ[σ] P) (hf : Function.Injective f) :
    IsNoetherian R M :=
  isNoetherian_of_linearEquiv (LinearEquiv.ofInjective f hf).symm

/--
theorem `fg_of_injective` / 定理 `fg_of_injective`

English:
theorem fg_of_injective
  statement: [IsNoetherian S P] {N : Submodule R M} {σ : R ->+* S} {σ' : S ->+* R}
  proof: haveI := isNoetherian_of_injective f hf
  IsNoetherian.noetherian N

中文:
定理 fg_of_injective
  结论: [是Noether S P] {N : 子模 R M} {σ : R ->+* S} {σ' : S ->+* R}
  证明: haveI := isNoetherian_of_injective f hf
  IsNoetherian.noetherian N

Depends on / 依赖: IsNoetherian, IsNoetherian.noetherian, isNoetherian_of_injective, noetherian
-/
theorem fg_of_injective [IsNoetherian S P] {N : Submodule R M} {σ : R ->+* S} {σ' : S ->+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ->ₛₗ[σ] P)
    (hf : Function.Injective f) : N.FG :=
  haveI := isNoetherian_of_injective f hf
  IsNoetherian.noetherian N

end

namespace Module

variable {R S M N : Type*}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
variable (R M)

-- see Note [lower instance priority]
instance (priority := 80) _root_.isNoetherian_of_finite [Finite M] : IsNoetherian R M :=
  ⟨fun s => ⟨(s : Set M).toFinite.toFinset, by rw [Set.Finite.coe_toFinset, Submodule.span_eq]⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) IsNoetherian.finite [IsNoetherian R M] : Module.Finite R M :=
  ⟨IsNoetherian.noetherian ⊤⟩

instance {R₁ S : Type*} [CommSemiring R₁] [Semiring S] [Algebra R₁ S]
    [IsNoetherian R₁ S] (I : Ideal S) : Module.Finite R₁ I :=
  IsNoetherian.finite R₁ ((I : Submodule S S).restrictScalars R₁)

variable {R M}

/--
theorem `Finite.of_injective` / 定理 `Finite.of_injective`

English:
theorem Finite.of_injective
  statement: [IsNoetherian S N] {σ : R ->+* S} {σ' : S ->+* R}
  proof: ⟨fg_of_injective f hf⟩

中文:
定理 有限.of_injective
  结论: [是Noether S N] {σ : R ->+* S} {σ' : S ->+* R}
  证明: ⟨fg_of_injective f hf⟩
-/
theorem Finite.of_injective [IsNoetherian S N] {σ : R ->+* S} {σ' : S ->+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ->ₛₗ[σ] N) (hf : Function.Injective f) :
    Module.Finite R M :=
  ⟨fg_of_injective f hf⟩

end Module

section

variable {R S M N P : Type*}
variable [Ring R] [Ring S] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module S P]

open IsNoetherian

/--
theorem `isNoetherian_of_ker_bot` / 定理 `isNoetherian_of_ker_bot`

English:
theorem isNoetherian_of_ker_bot
  statement: [IsNoetherian S P] {σ : R ->+* S} {σ' : S ->+* R}
  proof: isNoetherian_of_linearEquiv (LinearEquiv.ofInjective f <| LinearMap.ker_eq_bot.mp hf).symm

中文:
定理 isNoetherian_of_ker_bot
  结论: [是Noether S P] {σ : R ->+* S} {σ' : S ->+* R}
  证明: isNoetherian_of_linearEquiv (LinearEquiv.ofInjective f <| LinearMap.ker_eq_bot.mp hf).symm

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInjective, LinearMap, LinearMap.ker_eq_bot.mp, isNoetherian_of_linearEquiv, ker_eq_bot, ofInjective
-/
theorem isNoetherian_of_ker_bot [IsNoetherian S P] {σ : R ->+* S} {σ' : S ->+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ->ₛₗ[σ] P) (hf : LinearMap.ker f = ⊥) :
    IsNoetherian R M :=
  isNoetherian_of_linearEquiv (LinearEquiv.ofInjective f <| LinearMap.ker_eq_bot.mp hf).symm

/--
theorem `fg_of_ker_bot` / 定理 `fg_of_ker_bot`

English:
theorem fg_of_ker_bot
  statement: [IsNoetherian S P] {N : Submodule R M} {σ : R ->+* S} {σ' : S ->+* R}
  proof: haveI := isNoetherian_of_ker_bot f hf
  IsNoetherian.noetherian N

中文:
定理 fg_of_ker_bot
  结论: [是Noether S P] {N : 子模 R M} {σ : R ->+* S} {σ' : S ->+* R}
  证明: haveI := isNoetherian_of_ker_bot f hf
  IsNoetherian.noetherian N

Depends on / 依赖: IsNoetherian, IsNoetherian.noetherian, isNoetherian_of_ker_bot, noetherian
-/
theorem fg_of_ker_bot [IsNoetherian S P] {N : Submodule R M} {σ : R ->+* S} {σ' : S ->+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ->ₛₗ[σ] P) (hf : LinearMap.ker f = ⊥) :
    N.FG :=
  haveI := isNoetherian_of_ker_bot f hf
  IsNoetherian.noetherian N

-- False over a semiring: ℕ is a Noetherian ℕ-module but ℕ × ℕ is not.
/--
Instance `isNoetherian_prod` / 实例 `isNoetherian_prod`

English:
instance isNoetherian_prod
  signature: [IsNoetherian R M] [IsNoetherian R N]
  body: ⟨fun s =>
Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd R M N) (noetherian _)
      have : s ⊓ LinearMap.ker (LinearMap.snd R M N) <= LinearMap.range (LinearMap.inl R M N) :=
fun x ⟨_, hx2⟩ => ⟨x.1, Prod.ext rfl Eq.symm LinearMap.mem_ker.1 hx2⟩
      Submodule.map_comap_eq_self this ▸ (noether

中文:
实例 isNoetherian_prod
  签名: [是Noether R M] [是Noether R N]
  定义体: ⟨fun s =>
Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd R M N) (noetherian _)
      have : s ⊓ LinearMap.ker (LinearMap.snd R M N) <= LinearMap.range (LinearMap.inl R M N) :=
fun x ⟨_, hx2⟩ => ⟨x.1, Prod.ext rfl Eq.symm LinearMap.mem_ker.1 hx2⟩
      Submodule.map_comap_eq_self this ▸ (noether

Depends on / 依赖: Eq.symm, LinearMap, LinearMap.inl, LinearMap.ker, LinearMap.mem_ker, LinearMap.range, LinearMap.snd, Prod.ext, Submodule, Submodule.fg_of_fg_map_of_fg_inf_ker, Submodule.map_comap_eq_self, fg_of_fg_map_of_fg_inf_ker, map_comap_eq_self, mem_ker, noetherian
-/
instance isNoetherian_prod [IsNoetherian R M] [IsNoetherian R N] : IsNoetherian R (M × N) :=
  ⟨fun s =>
Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd R M N) (noetherian _)
      have : s ⊓ LinearMap.ker (LinearMap.snd R M N) <= LinearMap.range (LinearMap.inl R M N) :=
fun x ⟨_, hx2⟩ => ⟨x.1, Prod.ext rfl Eq.symm LinearMap.mem_ker.1 hx2⟩
      Submodule.map_comap_eq_self this ▸ (noetherian _).map _⟩

/--
Instance `isNoetherian_sup` / 实例 `isNoetherian_sup`

English:
instance isNoetherian_sup
  signature: (M₁ M₂ : Submodule R N) [IsNoetherian R M₁] [IsNoetherian R M₂]
  body: by
  have := isNoetherian_range (M₁.subtype.coprod M₂.subtype)
  rwa [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype] at this

中文:
实例 isNoetherian_sup
  签名: (M₁ M₂ : 子模 R N) [是Noether R M₁] [是Noether R M₂]
  定义体: by
  have := isNoetherian_range (M₁.subtype.coprod M₂.subtype)
  rwa [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype] at this

Depends on / 依赖: LinearMap, LinearMap.range_coprod, Submodule, Submodule.range_subtype, coprod, isNoetherian_range, range_coprod, range_subtype, subtype, subtype.coprod
-/
instance isNoetherian_sup (M₁ M₂ : Submodule R N) [IsNoetherian R M₁] [IsNoetherian R M₂] :
    IsNoetherian R ↥(M₁ ⊔ M₂) := by
  have := isNoetherian_range (M₁.subtype.coprod M₂.subtype)
  rwa [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype] at this

variable {ι : Type*} [Finite ι]

/--
Instance `isNoetherian_pi` / 实例 `isNoetherian_pi`

English:
instance isNoetherian_pi
  signature: :
  body: by
  apply Finite.induction_empty_option _ _ _ ι
  · exact fun e h => isNoetherian_of_linearEquiv (LinearEquiv.piCongrLeft R _ e)
  · infer_instance
  · exact fun ih => isNoetherian_of_linearEquiv (LinearEquiv.piOptionEquivProd R).symm

中文:
实例 isNoetherian_pi
  签名: :
  定义体: by
  apply Finite.induction_empty_option _ _ _ ι
  · exact fun e h => isNoetherian_of_linearEquiv (LinearEquiv.piCongrLeft R _ e)
  · infer_instance
  · exact fun ih => isNoetherian_of_linearEquiv (LinearEquiv.piOptionEquivProd R).symm

Depends on / 依赖: Finite, Finite.induction_empty_option, LinearEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piOptionEquivProd, induction_empty_option, infer_instance, isNoetherian_of_linearEquiv, piCongrLeft, piOptionEquivProd
-/
instance isNoetherian_pi :
    forall {M : ι -> Type*} [forall i, AddCommGroup (M i)]
      [forall i, Module R (M i)] [forall i, IsNoetherian R (M i)], IsNoetherian R (Π i, M i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · exact fun e h => isNoetherian_of_linearEquiv (LinearEquiv.piCongrLeft R _ e)
  · infer_instance
  · exact fun ih => isNoetherian_of_linearEquiv (LinearEquiv.piOptionEquivProd R).symm

/--
Instance `isNoetherian_pi'` / 实例 `isNoetherian_pi'`

English:
instance isNoetherian_pi'
  signature: [IsNoetherian R M]
  body: isNoetherian_pi

中文:
实例 isNoetherian_pi'
  签名: [是Noether R M]
  定义体: isNoetherian_pi

Depends on / 依赖: isNoetherian_pi
-/
instance isNoetherian_pi' [IsNoetherian R M] : IsNoetherian R (ι -> M) :=
  isNoetherian_pi

/--
Instance `isNoetherian_iSup` / 实例 `isNoetherian_iSup`

English:
instance isNoetherian_iSup
  signature: :
  body: by
  apply Finite.induction_empty_option _ _ _ ι
  · intro _ _ e h _ _; rw [← e.iSup_comp]; apply h
  · intros; rw [iSup_of_empty]; infer_instance
  · intro _ _ ih _ _; rw [iSup_option]; infer_instance

中文:
实例 isNoetherian_iSup
  签名: :
  定义体: by
  apply Finite.induction_empty_option _ _ _ ι
  · intro _ _ e h _ _; rw [← e.iSup_comp]; apply h
  · intros; rw [iSup_of_empty]; infer_instance
  · intro _ _ ih _ _; rw [iSup_option]; infer_instance

Depends on / 依赖: Finite, Finite.induction_empty_option, e.iSup_comp, iSup_comp, iSup_of_empty, iSup_option, induction_empty_option, infer_instance, intros
-/
instance isNoetherian_iSup :
    forall {M : ι -> Submodule R N} [forall i, IsNoetherian R (M i)], IsNoetherian R ↥(⨆ i, M i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · intro _ _ e h _ _; rw [← e.iSup_comp]; apply h
  · intros; rw [iSup_of_empty]; infer_instance
  · intro _ _ ih _ _; rw [iSup_option]; infer_instance

/--
theorem `isNoetherian_of_range_eq_ker` / 定理 `isNoetherian_of_range_eq_ker`

English:
theorem isNoetherian_of_range_eq_ker
  statement: {P : Type*} [AddCommGroup P] [Module R P] [IsNoetherian R M]
  proof: isNoetherian_mk
    wellFounded_gt_exact_sequence
      (LinearMap.range f)
      (Submodule.map ((LinearMap.ker f).liftQ f le_rfl))
      (Submodule.comap ((LinearMap.ker f).liftQ f le_rfl))
      (Submodule.comap g.rangeRestrict) (Submodule.map g.rangeRestrict)
      (Submodule.gciMapComap <| Line

中文:
定理 isNoetherian_of_range_eq_ker
  结论: {P : 类型} [加法交换群 P] [模 R P] [是Noether R M]
  证明: isNoetherian_mk
    wellFounded_gt_exact_sequence
      (LinearMap.range f)
      (Submodule.map ((LinearMap.ker f).liftQ f le_rfl))
      (Submodule.comap ((LinearMap.ker f).liftQ f le_rfl))
      (Submodule.comap g.rangeRestrict) (Submodule.map g.rangeRestrict)
      (Submodule.gciMapComap <| Line

Depends on / 依赖: LinearMap, LinearMap.ker, LinearMap.ker_eq_bot.mp, LinearMap.range, Submodule, Submodule.comap, Submodule.comap_map_eq, Submodule.gciMapComap, Submodule.giMapComap, Submodule.ker_liftQ_eq_bot, Submodule.map, Submodule.map_comap_eq, Submodule.range_liftQ, comap_map_eq, g.rangeRestrict, g.surjective_rangeRestrict, gciMapComap, giMapComap, inf_comm, isNoetherian_mk
-/
theorem isNoetherian_of_range_eq_ker {P : Type*} [AddCommGroup P] [Module R P] [IsNoetherian R M]
    [IsNoetherian R P] (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (h : LinearMap.range f = LinearMap.ker g) :
    IsNoetherian R N :=
isNoetherian_mk
    wellFounded_gt_exact_sequence
      (LinearMap.range f)
      (Submodule.map ((LinearMap.ker f).liftQ f le_rfl))
      (Submodule.comap ((LinearMap.ker f).liftQ f le_rfl))
      (Submodule.comap g.rangeRestrict) (Submodule.map g.rangeRestrict)
      (Submodule.gciMapComap <| LinearMap.ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
      (Submodule.giMapComap g.surjective_rangeRestrict)
      (by simp [Submodule.map_comap_eq, inf_comm, Submodule.range_liftQ])
      (by simp [Submodule.comap_map_eq, h])

/--
theorem `isNoetherian_iff_submodule_quotient` / 定理 `isNoetherian_iff_submodule_quotient`

English:
theorem isNoetherian_iff_submodule_quotient
  given: (S : Submodule R N)
  proof: by
  refine ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => ?_⟩
  apply isNoetherian_of_range_eq_ker S.subtype S.mkQ
  rw [Submodule.ker_mkQ]; rw [Submodule.range_subtype]

中文:
定理 isNoetherian_iff_submodule_quotient
  条件: (S : 子模 R N)
  证明: by
  refine ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => ?_⟩
  apply isNoetherian_of_range_eq_ker S.subtype S.mkQ
  rw [Submodule.ker_mkQ]; rw [Submodule.range_subtype]

Depends on / 依赖: S.mkQ, S.subtype, Submodule, Submodule.ker_mkQ, Submodule.range_subtype, isNoetherian_of_range_eq_ker, ker_mkQ, range_subtype, subtype
-/
theorem isNoetherian_iff_submodule_quotient (S : Submodule R N) :
    IsNoetherian R N ↔ IsNoetherian R S ∧ IsNoetherian R (N ⧸ S) := by
  refine ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => ?_⟩
  apply isNoetherian_of_range_eq_ker S.subtype S.mkQ
  rw [Submodule.ker_mkQ]; rw [Submodule.range_subtype]

end

section CommRing

variable (R M N : Type*) [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  [IsNoetherian R M] [Module.Finite R N]

/--
Instance `isNoetherian_linearMap_pi` / 实例 `isNoetherian_linearMap_pi`

English:
instance isNoetherian_linearMap_pi
  signature: {ι : Type*} [Finite ι]
  body: let _i : Fintype ι := Fintype.ofFinite ι; isNoetherian_of_linearEquiv (Module.piEquiv ι R M)

中文:
实例 isNoetherian_linearMap_pi
  签名: {ι : 类型} [有限 ι]
  定义体: let _i : Fintype ι := Fintype.ofFinite ι; isNoetherian_of_linearEquiv (Module.piEquiv ι R M)

Depends on / 依赖: Fintype, Fintype.ofFinite, Module, Module.piEquiv, isNoetherian_of_linearEquiv, ofFinite, piEquiv
-/
instance isNoetherian_linearMap_pi {ι : Type*} [Finite ι] : IsNoetherian R ((ι -> R) ->ₗ[R] M) :=
  let _i : Fintype ι := Fintype.ofFinite ι; isNoetherian_of_linearEquiv (Module.piEquiv ι R M)

/--
Instance `isNoetherian_linearMap` / 实例 `isNoetherian_linearMap`

English:
instance isNoetherian_linearMap
  signature: : IsNoetherian R (N ->ₗ[R] M)
  body: by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
  let g : (N ->ₗ[R] M) ->ₗ[R] (Fin n -> R) ->ₗ[R] M := (LinearMap.llcomp R (Fin n -> R) N M).flip f
  exact isNoetherian_of_injective g hf.injective_linearMapComp_right

中文:
实例 isNoetherian_linearMap
  签名: : 是Noether R (N ->ₗ[R] M)
  定义体: by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
  let g : (N ->ₗ[R] M) ->ₗ[R] (Fin n -> R) ->ₗ[R] M := (LinearMap.llcomp R (Fin n -> R) N M).flip f
  exact isNoetherian_of_injective g hf.injective_linearMapComp_right

Depends on / 依赖: Finite, LinearMap, LinearMap.llcomp, Module, Module.Finite.exists_fin, exists_fin, hf.injective_linearMapComp_right, injective_linearMapComp_right, isNoetherian_of_injective, llcomp
-/
instance isNoetherian_linearMap : IsNoetherian R (N ->ₗ[R] M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
  let g : (N ->ₗ[R] M) ->ₗ[R] (Fin n -> R) ->ₗ[R] M := (LinearMap.llcomp R (Fin n -> R) N M).flip f
  exact isNoetherian_of_injective g hf.injective_linearMapComp_right

end CommRing

open IsNoetherian Submodule Function

section

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/--
theorem `IsNoetherian.induction` / 定理 `IsNoetherian.induction`

English:
theorem IsNoetherian.induction
  statement: [IsNoetherian R M] {P : Submodule R M -> Prop}
  proof: IsWellFounded.induction _ I hgt

中文:
定理 是Noether.induction
  结论: [是Noether R M] {P : 子模 R M -> 命题}
  证明: IsWellFounded.induction _ I hgt

Depends on / 依赖: IsWellFounded, IsWellFounded.induction
-/
theorem IsNoetherian.induction [IsNoetherian R M] {P : Submodule R M -> Prop}
    (hgt : forall I, (forall J > I, P J) -> P I) (I : Submodule R M) : P I :=
  IsWellFounded.induction _ I hgt

/--
theorem `LinearMap.isNoetherian_iff_of_bijective` / 定理 `LinearMap.isNoetherian_iff_of_bijective`

English:
theorem LinearMap.isNoetherian_iff_of_bijective
  statement: {S P} [Semiring S] [AddCommMonoid P] [Module S P]
  proof: by
  simp_rw [isNoetherian_iff']
  let e := Submodule.orderIsoMapComapOfBijective l hl
  exact ⟨fun _ => e.symm.strictMono.wellFoundedGT, fun _ => e.strictMono.wellFoundedGT⟩

中文:
定理 线性映射.isNoetherian_iff_of_bijective
  结论: {S P} [半环 S] [加法交换幺半群 P] [模 S P]
  证明: by
  simp_rw [isNoetherian_iff']
  let e := Submodule.orderIsoMapComapOfBijective l hl
  exact ⟨fun _ => e.symm.strictMono.wellFoundedGT, fun _ => e.strictMono.wellFoundedGT⟩

Depends on / 依赖: Submodule, Submodule.orderIsoMapComapOfBijective, e.strictMono.wellFoundedGT, e.symm.strictMono.wellFoundedGT, isNoetherian_iff, orderIsoMapComapOfBijective, simp_rw, strictMono, wellFoundedGT
-/
theorem LinearMap.isNoetherian_iff_of_bijective {S P} [Semiring S] [AddCommMonoid P] [Module S P]
    {σ : R ->+* S} [RingHomSurjective σ] (l : M ->ₛₗ[σ] P) (hl : Function.Bijective l) :
    IsNoetherian R M ↔ IsNoetherian S P := by
  simp_rw [isNoetherian_iff']
  let e := Submodule.orderIsoMapComapOfBijective l hl
  exact ⟨fun _ => e.symm.strictMono.wellFoundedGT, fun _ => e.strictMono.wellFoundedGT⟩

end

section

variable {R M N P : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [IsNoetherian R M]

/--
lemma `Submodule.finite_ne_bot_of_iSupIndep` / 引理 `Submodule.finite_ne_bot_of_iSupIndep`

English:
lemma Submodule.finite_ne_bot_of_iSupIndep
  given: {ι : Type*} {N : ι -> Submodule R M} (h : iSupIndep N)
  proof: WellFoundedGT.finite_ne_bot_of_iSupIndep h

中文:
引理 子模.finite_ne_bot_of_iSupIndep
  条件: {ι : 类型} {N : ι -> 子模 R M} (h : iSupIndep N)
  证明: WellFoundedGT.finite_ne_bot_of_iSupIndep h

Depends on / 依赖: WellFoundedGT, WellFoundedGT.finite_ne_bot_of_iSupIndep, finite_ne_bot_of_iSupIndep
-/
lemma Submodule.finite_ne_bot_of_iSupIndep {ι : Type*} {N : ι -> Submodule R M} (h : iSupIndep N) :
    Set.Finite {i | N i != ⊥} :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep h

/--
theorem `LinearIndependent.finite_of_isNoetherian` / 定理 `LinearIndependent.finite_of_isNoetherian`

English:
theorem LinearIndependent.finite_of_isNoetherian
  statement: [Nontrivial R] {ι} {v : ι -> M}
  proof: WellFoundedGT.finite_of_iSupIndep hv.iSupIndep_span_singleton fun i _ => hv.ne_zero i (by simp_all)

中文:
定理 LinearIndependent.finite_of_isNoetherian
  结论: [非平凡 R] {ι} {v : ι -> M}
  证明: WellFoundedGT.finite_of_iSupIndep hv.iSupIndep_span_singleton fun i _ => hv.ne_zero i (by simp_all)

Depends on / 依赖: WellFoundedGT, WellFoundedGT.finite_of_iSupIndep, finite_of_iSupIndep, hv.iSupIndep_span_singleton, hv.ne_zero, iSupIndep_span_singleton, ne_zero
-/
theorem LinearIndependent.finite_of_isNoetherian [Nontrivial R] {ι} {v : ι -> M}
    (hv : LinearIndependent R v) : Finite ι :=
  WellFoundedGT.finite_of_iSupIndep hv.iSupIndep_span_singleton fun i _ => hv.ne_zero i (by simp_all)

variable [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P] [Nontrivial P]

/--
theorem `IsNoetherian.subsingleton_of_injective` / 定理 `IsNoetherian.subsingleton_of_injective`

English:
theorem IsNoetherian.subsingleton_of_injective
  statement: {P : Type*} [AddCommMonoid P] [Module R P]
  proof: subsingleton_of_forall_eq 0 fun p => by_contra fun _ =>
    have ⟨g, inj⟩ := LinearMap.exists_finsupp_nat_of_prod_injective inj
Infinite.not_finite WellFoundedGT.finite_of_iSupIndep
      (g.iSupIndep_map inj (iSupIndep_range_lsingle Nat R P))
      fun i => (Submodule.ne_bot_iff _).mpr ⟨_, ⟨_, ⟨p, 

中文:
定理 是Noether.subsingleton_of_injective
  结论: {P : 类型} [加法交换幺半群 P] [模 R P]
  证明: subsingleton_of_forall_eq 0 fun p => by_contra fun _ =>
    have ⟨g, inj⟩ := LinearMap.exists_finsupp_nat_of_prod_injective inj
Infinite.not_finite WellFoundedGT.finite_of_iSupIndep
      (g.iSupIndep_map inj (iSupIndep_range_lsingle Nat R P))
      fun i => (Submodule.ne_bot_iff _).mpr ⟨_, ⟨_, ⟨p, 

Depends on / 依赖: Infinite, Infinite.not_finite, LinearMap, LinearMap.exists_finsupp_nat_of_prod_injective, Submodule, Submodule.ne_bot_iff, WellFoundedGT, WellFoundedGT.finite_of_iSupIndep, exists_finsupp_nat_of_prod_injective, finite_of_iSupIndep, g.iSupIndep_map, iSupIndep_map, iSupIndep_range_lsingle, ne_bot_iff, not_finite, subsingleton_of_forall_eq
-/
theorem IsNoetherian.subsingleton_of_injective {P : Type*} [AddCommMonoid P] [Module R P]
    {f : P × M ->ₗ[R] M} (inj : Injective f) : Subsingleton P :=
  subsingleton_of_forall_eq 0 fun p => by_contra fun _ =>
    have ⟨g, inj⟩ := LinearMap.exists_finsupp_nat_of_prod_injective inj
Infinite.not_finite WellFoundedGT.finite_of_iSupIndep
      (g.iSupIndep_map inj (iSupIndep_range_lsingle Nat R P))
      fun i => (Submodule.ne_bot_iff _).mpr ⟨_, ⟨_, ⟨p, rfl⟩, rfl⟩, by simpa [inj]⟩

/--
theorem `LinearIndependent.set_finite_of_isNoetherian` / 定理 `LinearIndependent.set_finite_of_isNoetherian`

English:
theorem LinearIndependent.set_finite_of_isNoetherian
  statement: [Nontrivial R] {s : Set M}
  proof: hi.finite_of_isNoetherian

中文:
定理 LinearIndependent.set_finite_of_isNoetherian
  结论: [非平凡 R] {s : 集合 M}
  证明: hi.finite_of_isNoetherian

Depends on / 依赖: finite_of_isNoetherian, hi.finite_of_isNoetherian
-/
theorem LinearIndependent.set_finite_of_isNoetherian [Nontrivial R] {s : Set M}
    (hi : LinearIndependent R ((↑) : s -> M)) : s.Finite :=
  hi.finite_of_isNoetherian

/--
theorem `IsNoetherian.disjoint_partialSups_eventually_bot` / 定理 `IsNoetherian.disjoint_partialSups_eventually_bot`

English:
theorem IsNoetherian.disjoint_partialSups_eventually_bot
  proof: by
  -- A little off-by-one cleanup first:
  suffices t : exists n : Nat, forall m, n <= m -> f (m + 1) = ⊥ by
    obtain ⟨n, w⟩ := t
    use n + 1
    rintro (_ | m) p
    · cases p
    · apply w
      exact Nat.succ_le_succ_iff.mp p
  obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr inferIn

中文:
定理 是Noether.disjoint_partialSups_eventually_bot
  证明: by
  -- A little off-by-one cleanup first:
  suffices t : exists n : Nat, forall m, n <= m -> f (m + 1) = ⊥ by
    obtain ⟨n, w⟩ := t
    use n + 1
    rintro (_ | m) p
    · cases p
    · apply w
      exact Nat.succ_le_succ_iff.mp p
  obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr inferIn
-/
theorem IsNoetherian.disjoint_partialSups_eventually_bot
    (f : Nat -> Submodule R M) (h : forall n, Disjoint (partialSups f n) (f (n + 1))) :
    exists n : Nat, forall m, n <= m -> f m = ⊥ := by
  -- A little off-by-one cleanup first:
  suffices t : exists n : Nat, forall m, n <= m -> f (m + 1) = ⊥ by
    obtain ⟨n, w⟩ := t
    use n + 1
    rintro (_ | m) p
    · cases p
    · apply w
      exact Nat.succ_le_succ_iff.mp p
  obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance (partialSups f)
refine ⟨n, fun m p => (h m).eq_bot_of_ge sup_eq_left.mp ?_⟩
simpa only [partialSups_add_one] using (w (m + 1) <| le_add_right p).symm.trans w m p

end

-- see Note [lower instance priority]
/-- Modules over the trivial ring are Noetherian. -/
instance (priority := 100) isNoetherian_of_subsingleton (R M) [Subsingleton R] [Semiring R]
    [AddCommMonoid M] [Module R M] : IsNoetherian R M :=
  haveI := Module.subsingleton R M
  isNoetherian_of_finite R M

/--
theorem `isNoetherian_of_submodule_of_noetherian` / 定理 `isNoetherian_of_submodule_of_noetherian`

English:
theorem isNoetherian_of_submodule_of_noetherian
  statement: (R M) [Semiring R] [AddCommMonoid M] [Module R M]
  proof: isNoetherian_mk ⟨OrderEmbedding.wellFounded (Submodule.MapSubtype.orderEmbedding N).dual h.wf⟩

中文:
定理 isNoetherian_of_submodule_of_noetherian
  结论: (R M) [半环 R] [加法交换幺半群 M] [模 R M]
  证明: isNoetherian_mk ⟨OrderEmbedding.wellFounded (Submodule.MapSubtype.orderEmbedding N).dual h.wf⟩

Depends on / 依赖: MapSubtype, OrderEmbedding, OrderEmbedding.wellFounded, Submodule, Submodule.MapSubtype.orderEmbedding, h.wf, isNoetherian_mk, orderEmbedding, wellFounded
-/
theorem isNoetherian_of_submodule_of_noetherian (R M) [Semiring R] [AddCommMonoid M] [Module R M]
    (N : Submodule R M) (h : IsNoetherian R M) : IsNoetherian R N :=
  isNoetherian_mk ⟨OrderEmbedding.wellFounded (Submodule.MapSubtype.orderEmbedding N).dual h.wf⟩

/--
theorem `isNoetherian_of_tower` / 定理 `isNoetherian_of_tower`

English:
theorem isNoetherian_of_tower
  statement: (R) {S M} [Semiring R] [Semiring S] [AddCommMonoid M] [SMul R S]
  proof: isNoetherian_mk ⟨(Submodule.restrictScalarsEmbedding R S M).dual.wellFounded h.wf⟩

中文:
定理 isNoetherian_of_tower
  结论: (R) {S M} [半环 R] [半环 S] [加法交换幺半群 M] [标量乘法 R S]
  证明: isNoetherian_mk ⟨(Submodule.restrictScalarsEmbedding R S M).dual.wellFounded h.wf⟩

Depends on / 依赖: Submodule, Submodule.restrictScalarsEmbedding, dual.wellFounded, h.wf, isNoetherian_mk, restrictScalarsEmbedding, wellFounded
-/
theorem isNoetherian_of_tower (R) {S M} [Semiring R] [Semiring S] [AddCommMonoid M] [SMul R S]
    [Module S M] [Module R M] [IsScalarTower R S M] (h : IsNoetherian R M) : IsNoetherian S M :=
  isNoetherian_mk ⟨(Submodule.restrictScalarsEmbedding R S M).dual.wellFounded h.wf⟩

/--
Instance `isNoetherian_of_isNoetherianRing_of_finite` / 实例 `isNoetherian_of_isNoetherianRing_of_finite`

English:
instance isNoetherian_of_isNoetherianRing_of_finite
  signature: (R M : Type*)
  body: have ⟨_, _, h⟩ := Module.Finite.exists_fin' R M
  isNoetherian_of_surjective _ (LinearMap.range_eq_top.mpr h)

中文:
实例 isNoetherian_of_isNoetherianRing_of_finite
  签名: (R M : 类型)
  定义体: have ⟨_, _, h⟩ := Module.Finite.exists_fin' R M
  isNoetherian_of_surjective _ (LinearMap.range_eq_top.mpr h)

Depends on / 依赖: Finite, LinearMap, LinearMap.range_eq_top.mpr, Module, Module.Finite.exists_fin, exists_fin, isNoetherian_of_surjective, range_eq_top
-/
instance isNoetherian_of_isNoetherianRing_of_finite (R M : Type*)
    [Ring R] [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M] :
    IsNoetherian R M :=
  have ⟨_, _, h⟩ := Module.Finite.exists_fin' R M
  isNoetherian_of_surjective _ (LinearMap.range_eq_top.mpr h)

/--
theorem `isNoetherian_of_fg_of_noetherian` / 定理 `isNoetherian_of_fg_of_noetherian`

English:
theorem isNoetherian_of_fg_of_noetherian
  statement: {R M} [Ring R] [AddCommGroup M] [Module R M]
  proof: haveI : Module.Finite R N := .of_fg hN; inferInstance

中文:
定理 isNoetherian_of_fg_of_noetherian
  结论: {R M} [环 R] [加法交换群 M] [模 R M]
  证明: haveI : Module.Finite R N := .of_fg hN; inferInstance

Depends on / 依赖: Finite, Module, Module.Finite, of_fg
-/
theorem isNoetherian_of_fg_of_noetherian {R M} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [I : IsNoetherianRing R] (hN : N.FG) : IsNoetherian R N :=
  haveI : Module.Finite R N := .of_fg hN; inferInstance

/--
theorem `isNoetherian_span_of_finite` / 定理 `isNoetherian_span_of_finite`

English:
theorem isNoetherian_span_of_finite
  statement: (R) {M} [Ring R] [AddCommGroup M] [Module R M]
  proof: isNoetherian_of_fg_of_noetherian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)

中文:
定理 isNoetherian_span_of_finite
  结论: (R) {M} [环 R] [加法交换群 M] [模 R M]
  证明: isNoetherian_of_fg_of_noetherian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)

Depends on / 依赖: Submodule, Submodule.fg_def.mpr, fg_def, isNoetherian_of_fg_of_noetherian
-/
theorem isNoetherian_span_of_finite (R) {M} [Ring R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] {A : Set M} (hA : A.Finite) : IsNoetherian R (Submodule.span R A) :=
  isNoetherian_of_fg_of_noetherian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)

/--
theorem `IsNoetherianRing.of_finite` / 定理 `IsNoetherianRing.of_finite`

English:
theorem IsNoetherianRing.of_finite
  statement: (R S) [Ring R] [Ring S] [Module R S] [IsScalarTower R S S]
  proof: isNoetherian_of_tower R inferInstance

中文:
定理 是Noether环.of_finite
  结论: (R S) [环 R] [环 S] [模 R S] [标量塔 R S S]
  证明: isNoetherian_of_tower R inferInstance

Depends on / 依赖: isNoetherian_of_tower
-/
theorem IsNoetherianRing.of_finite (R S) [Ring R] [Ring S] [Module R S] [IsScalarTower R S S]
    [IsNoetherianRing R] [Module.Finite R S] : IsNoetherianRing S :=
  isNoetherian_of_tower R inferInstance

/--
theorem `isNoetherianRing_of_surjective` / 定理 `isNoetherianRing_of_surjective`

English:
theorem isNoetherianRing_of_surjective
  statement: (R) [Semiring R] (S) [Semiring S] (f : R ->+* S)
  proof: isNoetherian_mk ⟨OrderEmbedding.wellFounded (Ideal.orderEmbeddingOfSurjective f hf).dual H.wf⟩

中文:
定理 isNoetherianRing_of_surjective
  结论: (R) [半环 R] (S) [半环 S] (f : R ->+* S)
  证明: isNoetherian_mk ⟨OrderEmbedding.wellFounded (Ideal.orderEmbeddingOfSurjective f hf).dual H.wf⟩

Depends on / 依赖: H.wf, Ideal.orderEmbeddingOfSurjective, OrderEmbedding, OrderEmbedding.wellFounded, isNoetherian_mk, orderEmbeddingOfSurjective, wellFounded
-/
theorem isNoetherianRing_of_surjective (R) [Semiring R] (S) [Semiring S] (f : R ->+* S)
    (hf : Function.Surjective f) [H : IsNoetherianRing R] : IsNoetherianRing S :=
  isNoetherian_mk ⟨OrderEmbedding.wellFounded (Ideal.orderEmbeddingOfSurjective f hf).dual H.wf⟩

/--
Instance `isNoetherianRing_rangeS` / 实例 `isNoetherianRing_rangeS`

English:
instance isNoetherianRing_rangeS
  signature: {R} [Semiring R] {S} [Semiring S] (f : R ->+* S)
  body: isNoetherianRing_of_surjective R f.rangeS f.rangeSRestrict f.rangeSRestrict_surjective

中文:
实例 isNoetherianRing_rangeS
  签名: {R} [半环 R] {S} [半环 S] (f : R ->+* S)
  定义体: isNoetherianRing_of_surjective R f.rangeS f.rangeSRestrict f.rangeSRestrict_surjective

Depends on / 依赖: f.rangeS, f.rangeSRestrict, f.rangeSRestrict_surjective, isNoetherianRing_of_surjective, rangeS, rangeSRestrict, rangeSRestrict_surjective
-/
instance isNoetherianRing_rangeS {R} [Semiring R] {S} [Semiring S] (f : R ->+* S)
    [IsNoetherianRing R] : IsNoetherianRing f.rangeS :=
  isNoetherianRing_of_surjective R f.rangeS f.rangeSRestrict f.rangeSRestrict_surjective

/--
Instance `isNoetherianRing_range` / 实例 `isNoetherianRing_range`

English:
instance isNoetherianRing_range
  signature: {R} [Ring R] {S} [Ring S] (f : R ->+* S)
  body: isNoetherianRing_rangeS f

中文:
实例 isNoetherianRing_range
  签名: {R} [环 R] {S} [环 S] (f : R ->+* S)
  定义体: isNoetherianRing_rangeS f

Depends on / 依赖: ClosedSubmodule, ClosedSubmodule.carrier_eq_coe, IsComplete, IsComplete.completeSpace_coe, K.isClosed, carrier_eq_coe, completeSpace_coe, isClosed, isComplete, isNoetherianRing_rangeS
-/
instance isNoetherianRing_range {R} [Ring R] {S} [Ring S] (f : R ->+* S)
    [IsNoetherianRing R] : IsNoetherianRing f.range :=
  isNoetherianRing_rangeS f

/--
theorem `isNoetherianRing_of_ringEquiv` / 定理 `isNoetherianRing_of_ringEquiv`

English:
theorem isNoetherianRing_of_ringEquiv
  statement: (R) [Semiring R] {S} [Semiring S] (f : R ≃+* S)
  proof: isNoetherianRing_of_surjective R S f.toRingHom f.toEquiv.surjective

中文:
定理 isNoetherianRing_of_ringEquiv
  结论: (R) [半环 R] {S} [半环 S] (f : R ≃+* S)
  证明: isNoetherianRing_of_surjective R S f.toRingHom f.toEquiv.surjective

Depends on / 依赖: f.toEquiv.surjective, f.toRingHom, isNoetherianRing_of_surjective, surjective, toEquiv, toRingHom
-/
theorem isNoetherianRing_of_ringEquiv (R) [Semiring R] {S} [Semiring S] (f : R ≃+* S)
    [IsNoetherianRing R] : IsNoetherianRing S :=
  isNoetherianRing_of_surjective R S f.toRingHom f.toEquiv.surjective

instance {R S} [Semiring R] [Semiring S] [IsNoetherianRing R] [IsNoetherianRing S] :
    IsNoetherianRing (R × S) := by
  rw [IsNoetherianRing]; rw [isNoetherian_iff'] at *
  exact Ideal.idealProdEquiv.toOrderEmbedding.wellFoundedGT

instance {ι} [Finite ι] : forall {R : ι -> Type*} [Π i, Semiring (R i)] [forall i, IsNoetherianRing (R i)],
    IsNoetherianRing (Π i, R i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · exact fun e h => isNoetherianRing_of_ringEquiv _ (.piCongrLeft _ e)
  · infer_instance
  · exact fun ih => isNoetherianRing_of_ringEquiv _ (.symm .piOptionEquivProd)

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/--
theorem `FG.of_le_of_isNoetherian` / 定理 `FG.of_le_of_isNoetherian`

English:
theorem FG.of_le_of_isNoetherian
  given: {S T : Submodule R M} [IsNoetherian R T] (hST : S <= T)
  statement: S.FG
  proof: isNoetherian_submodule.mp inferInstance _ hST

中文:
定理 FG.of_le_of_isNoetherian
  条件: {S T : 子模 R M} [是Noether R T] (hST : S <= T)
  结论: S.FG
  证明: isNoetherian_submodule.mp inferInstance _ hST

Depends on / 依赖: isNoetherian_submodule, isNoetherian_submodule.mp
-/
theorem FG.of_le_of_isNoetherian {S T : Submodule R M} [IsNoetherian R T] (hST : S <= T) : S.FG :=
  isNoetherian_submodule.mp inferInstance _ hST

/--
lemma `FG.of_le` / 引理 `FG.of_le`

English:
lemma FG.of_le
  given: [IsNoetherianRing R] {S T : Submodule R M} (hT : T.FG) (hST : S <= T)
  statement: S.FG
  proof: by
  rw [← Module.Finite.iff_fg] at hT
  exact FG.of_le_of_isNoetherian hST

中文:
引理 FG.of_le
  条件: [是Noether环 R] {S T : 子模 R M} (hT : T.FG) (hST : S <= T)
  结论: S.FG
  证明: by
  rw [← Module.Finite.iff_fg] at hT
  exact FG.of_le_of_isNoetherian hST

Depends on / 依赖: FG.of_le_of_isNoetherian, Finite, Module, Module.Finite.iff_fg, iff_fg, of_le_of_isNoetherian
-/
lemma FG.of_le [IsNoetherianRing R] {S T : Submodule R M} (hT : T.FG) (hST : S <= T) : S.FG := by
  rw [← Module.Finite.iff_fg] at hT
  exact FG.of_le_of_isNoetherian hST

/--
theorem `FG.of_disjoint_of_isNoetherian_quotient` / 定理 `FG.of_disjoint_of_isNoetherian_quotient`

English:
theorem FG.of_disjoint_of_isNoetherian_quotient
  statement: {S T : Submodule R M} [IsNoetherian R (M ⧸ T)]
  proof: Module.Finite.iff_fg.mp .of_injective (T.mkQ.domRestrict S) (by simp [hST])

中文:
定理 FG.of_disjoint_of_isNoetherian_quotient
  结论: {S T : 子模 R M} [是Noether R (M ⧸ T)]
  证明: Module.Finite.iff_fg.mp .of_injective (T.mkQ.domRestrict S) (by simp [hST])

Depends on / 依赖: Finite, IsNoetherianRing, IsNoetherianRing.isClosed_ideal, Module, Module.Finite.iff_fg.mp, T.mkQ.domRestrict, domRestrict, iff_fg, isClosed_ideal, of_injective
-/
theorem FG.of_disjoint_of_isNoetherian_quotient {S T : Submodule R M} [IsNoetherian R (M ⧸ T)]
    (hST : Disjoint S T) : S.FG :=
Module.Finite.iff_fg.mp .of_injective (T.mkQ.domRestrict S) (by simp [hST])

end Submodule

universe w v u

variable (R : Type u) [CommRing R]

/--
theorem `Module.exists_finite_presentation` / 定理 `Module.exists_finite_presentation`

English:
theorem Module.exists_finite_presentation
  statement: [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]
  proof: by
  rcases Module.Finite.exists_fin' R M with ⟨m, f', hf'⟩
  let f := f'.comp ((Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)).trans
      (Finsupp.linearEquivFunOnFinite R R (Fin m))).1
  use (Fin m ->₀ Shrink.{v, u} R), inferInstance, inferInstance, inferInstance, inferInstance, f
  s

中文:
定理 模.存在_finite_presentation
  结论: [Small.{v} R] (M : 类型v) [加法交换群 M] [模 R M]
  证明: by
  rcases Module.Finite.exists_fin' R M with ⟨m, f', hf'⟩
  let f := f'.comp ((Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)).trans
      (Finsupp.linearEquivFunOnFinite R R (Fin m))).1
  use (Fin m ->₀ Shrink.{v, u} R), inferInstance, inferInstance, inferInstance, inferInstance, f
  s

Depends on / 依赖: Finite, Finsupp, Finsupp.linearEquivFunOnFinite, Finsupp.mapRange.linearEquiv, Module, Module.Finite.exists_fin, Shrink, Shrink.linearEquiv, exists_fin, linearEquiv, linearEquivFunOnFinite, mapRange
-/
theorem Module.exists_finite_presentation [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : exists (P : Type v) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Free R P)
      (_ : Module.Finite R P) (f : P ->ₗ[R] M), Function.Surjective f := by
  rcases Module.Finite.exists_fin' R M with ⟨m, f', hf'⟩
  let f := f'.comp ((Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)).trans
      (Finsupp.linearEquivFunOnFinite R R (Fin m))).1
  use (Fin m ->₀ Shrink.{v, u} R), inferInstance, inferInstance, inferInstance, inferInstance, f
  simpa [f] using hf'
