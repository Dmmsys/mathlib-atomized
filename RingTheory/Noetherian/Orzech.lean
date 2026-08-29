/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard
-/
module

public import Mathlib.Algebra.Module.Submodule.IterateMapComap
public import Mathlib.Order.PartialSups
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.OrzechProperty

/-!
# Noetherian rings have the Orzech property

## Main results

* `IsNoetherian.injective_of_surjective_of_injective`: if `M` and `N` are `R`-modules for a ring `R`
  (not necessarily commutative), `M` is Noetherian, `i : N →ₗ[R] M` is injective,
  `f : N →ₗ[R] M` is surjective, then `f` is also injective.
* `IsNoetherianRing.orzechProperty`: Any Noetherian ring satisfies the Orzech property.
-/

@[expose] public section


open Set Filter Pointwise

open IsNoetherian Submodule Function

section

universe w

variable {R M P : Type*} {N : Type w} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup P] [Module R P] [IsNoetherian R M]

/--
theorem `IsNoetherian.injective_of_surjective_of_injective` / 定理 `IsNoetherian.injective_of_surjective_of_injective`

English:
theorem IsNoetherian.injective_of_surjective_of_injective
  statement: (i f : N ->ₗ[R] M)
  proof: by
  have := isNoetherian_of_injective i hi
  obtain ⟨n, H⟩ := monotone_stabilizes_iff_noetherian.2 ‹_›
⟨_, monotone_nat_of_le_succ f.iterateMapComap_le_succ i ⊥ (by simp)⟩
exact LinearMap.ker_eq_bot.1 bot_unique
    f.ker_le_of_iterateMapComap_eq_succ i ⊥ n (H _ (Nat.le_succ _)) hf hi

中文:
定理 IsNoetherian.injective_of_surjective_of_injective
  结论: (i f : N ->ₗ[R] M)
  证明: by
  have := isNoetherian_of_injective i hi
  obtain ⟨n, H⟩ := monotone_stabilizes_iff_noetherian.2 ‹_›
⟨_, monotone_nat_of_le_succ f.iterateMapComap_le_succ i ⊥ (by simp)⟩
exact LinearMap.ker_eq_bot.1 bot_unique
    f.ker_le_of_iterateMapComap_eq_succ i ⊥ n (H _ (Nat.le_succ _)) hf hi

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, Nat.le_succ, bot_unique, f.iterateMapComap_le_succ, f.ker_le_of_iterateMapComap_eq_succ, isNoetherian_of_injective, iterateMapComap_le_succ, ker_eq_bot, ker_le_of_iterateMapComap_eq_succ, le_succ, monotone_nat_of_le_succ, monotone_stabilizes_iff_noetherian
-/
theorem IsNoetherian.injective_of_surjective_of_injective (i f : N ->ₗ[R] M)
    (hi : Injective i) (hf : Surjective f) : Injective f := by
  have := isNoetherian_of_injective i hi
  obtain ⟨n, H⟩ := monotone_stabilizes_iff_noetherian.2 ‹_›
⟨_, monotone_nat_of_le_succ f.iterateMapComap_le_succ i ⊥ (by simp)⟩
exact LinearMap.ker_eq_bot.1 bot_unique
    f.ker_le_of_iterateMapComap_eq_succ i ⊥ n (H _ (Nat.le_succ _)) hf hi

/--
theorem `IsNoetherian.injective_of_surjective_of_submodule` / 定理 `IsNoetherian.injective_of_surjective_of_submodule`

English:
theorem IsNoetherian.injective_of_surjective_of_submodule
  proof: IsNoetherian.injective_of_surjective_of_injective N.subtype f N.injective_subtype hf

中文:
定理 IsNoetherian.injective_of_surjective_of_submodule
  证明: IsNoetherian.injective_of_surjective_of_injective N.subtype f N.injective_subtype hf

Depends on / 依赖: IsNoetherian, IsNoetherian.injective_of_surjective_of_injective, N.injective_subtype, N.subtype, injective_of_surjective_of_injective, injective_subtype, subtype
-/
theorem IsNoetherian.injective_of_surjective_of_submodule
    {N : Submodule R M} (f : N ->ₗ[R] M) (hf : Surjective f) : Injective f :=
  IsNoetherian.injective_of_surjective_of_injective N.subtype f N.injective_subtype hf

/--
theorem `IsNoetherian.injective_of_surjective_endomorphism` / 定理 `IsNoetherian.injective_of_surjective_endomorphism`

English:
theorem IsNoetherian.injective_of_surjective_endomorphism
  statement: (f : M ->ₗ[R] M)
  proof: IsNoetherian.injective_of_surjective_of_injective _ f (LinearEquiv.refl _ _).injective s

中文:
定理 IsNoetherian.injective_of_surjective_endomorphism
  结论: (f : M ->ₗ[R] M)
  证明: IsNoetherian.injective_of_surjective_of_injective _ f (LinearEquiv.refl _ _).injective s

Depends on / 依赖: IsNoetherian, IsNoetherian.injective_of_surjective_of_injective, LinearEquiv, LinearEquiv.refl, injective, injective_of_surjective_of_injective
-/
theorem IsNoetherian.injective_of_surjective_endomorphism (f : M ->ₗ[R] M)
    (s : Surjective f) : Injective f :=
  IsNoetherian.injective_of_surjective_of_injective _ f (LinearEquiv.refl _ _).injective s

/--
theorem `IsNoetherian.bijective_of_surjective_endomorphism` / 定理 `IsNoetherian.bijective_of_surjective_endomorphism`

English:
theorem IsNoetherian.bijective_of_surjective_endomorphism
  statement: (f : M ->ₗ[R] M)
  proof: ⟨IsNoetherian.injective_of_surjective_endomorphism f s, s⟩

中文:
定理 IsNoetherian.bijective_of_surjective_endomorphism
  结论: (f : M ->ₗ[R] M)
  证明: ⟨IsNoetherian.injective_of_surjective_endomorphism f s, s⟩

Depends on / 依赖: IsNoetherian, IsNoetherian.injective_of_surjective_endomorphism, injective_of_surjective_endomorphism
-/
theorem IsNoetherian.bijective_of_surjective_endomorphism (f : M ->ₗ[R] M)
    (s : Surjective f) : Bijective f :=
  ⟨IsNoetherian.injective_of_surjective_endomorphism f s, s⟩

/--
theorem `IsNoetherian.subsingleton_of_prod_injective` / 定理 `IsNoetherian.subsingleton_of_prod_injective`

English:
theorem IsNoetherian.subsingleton_of_prod_injective
  statement: (f : M × N ->ₗ[R] M)
  proof: .intro fun x y => by
  have h := IsNoetherian.injective_of_surjective_of_injective f _ i LinearMap.fst_surjective
  simpa using h (show LinearMap.fst R M N (0, x) = LinearMap.fst R M N (0, y) from rfl)

中文:
定理 IsNoetherian.subsingleton_of_prod_injective
  结论: (f : M × N ->ₗ[R] M)
  证明: .intro fun x y => by
  have h := IsNoetherian.injective_of_surjective_of_injective f _ i LinearMap.fst_surjective
  simpa using h (show LinearMap.fst R M N (0, x) = LinearMap.fst R M N (0, y) from rfl)

Depends on / 依赖: IsNoetherian, IsNoetherian.injective_of_surjective_of_injective, LinearMap, LinearMap.fst, LinearMap.fst_surjective, fst_surjective, injective_of_surjective_of_injective
-/
theorem IsNoetherian.subsingleton_of_prod_injective (f : M × N ->ₗ[R] M)
    (i : Injective f) : Subsingleton N := .intro fun x y => by
  have h := IsNoetherian.injective_of_surjective_of_injective f _ i LinearMap.fst_surjective
  simpa using h (show LinearMap.fst R M N (0, x) = LinearMap.fst R M N (0, y) from rfl)

/-- If `M ⊕ N` embeds into `M`, for `M` Noetherian over `R`, then `N` is trivial. -/
@[simps!]
/--
Definition of `IsNoetherian.equivPUnitOfProdInjective` / `IsNoetherian.equivPUnitOfProdInjective` 的定义

English:
definition IsNoetherian.equivPUnitOfProdInjective
  signature: (f : M × N ->ₗ[R] M)
  body: haveI := IsNoetherian.subsingleton_of_prod_injective f i
  .ofSubsingleton _ _

中文:
定义 IsNoetherian.equivPUnitOfProdInjective
  签名: (f : M × N ->ₗ[R] M)
  定义体: haveI := IsNoetherian.subsingleton_of_prod_injective f i
  .ofSubsingleton _ _

Depends on / 依赖: IsNoetherian, IsNoetherian.subsingleton_of_prod_injective, ofSubsingleton, subsingleton_of_prod_injective
-/
def IsNoetherian.equivPUnitOfProdInjective (f : M × N ->ₗ[R] M)
    (i : Injective f) : N ≃ₗ[R] PUnit.{w + 1} :=
  haveI := IsNoetherian.subsingleton_of_prod_injective f i
  .ofSubsingleton _ _

end

/-- Any Noetherian ring satisfies Orzech property.
See also `IsNoetherian.injective_of_surjective_of_submodule` and
`IsNoetherian.injective_of_surjective_of_injective`. -/
instance (priority := 100) IsNoetherianRing.orzechProperty
    (R) [Ring R] [IsNoetherianRing R] : OrzechProperty R where
  injective_of_surjective_of_submodule' {M} :=
    letI := Module.addCommMonoidToAddCommGroup R (M := M)
    IsNoetherian.injective_of_surjective_of_submodule
