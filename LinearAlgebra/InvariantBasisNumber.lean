/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Noetherian.Orzech
public import Mathlib.RingTheory.OrzechProperty
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Invariant basis number property

## Main definitions

Let `R` be a (not necessary commutative) ring.

- `InvariantBasisNumber R` is a type class stating that `(Fin n → R) ≃ₗ[R] (Fin m → R)`
  implies `n = m`, a property known as the *invariant basis number property.*

  This assumption implies that there is a well-defined notion of the rank
  of a finitely generated free (left) `R`-module.

It is also useful to consider the following stronger conditions:

- The *rank condition*, witnessed by the type class `RankCondition R`, states that
  the existence of a surjective linear map `(Fin n → R) →ₗ[R] (Fin m → R)` implies `m ≤ n`.

- The *strong rank condition*, witnessed by the type class `StrongRankCondition R`, states
  that the existence of an injective linear map `(Fin n → R) →ₗ[R] (Fin m → R)`
  implies `n ≤ m`.

- `OrzechProperty R`, defined in `Mathlib/RingTheory/OrzechProperty.lean`,
  states that for any finitely generated `R`-module `M`, any surjective homomorphism `f : N → M`
  from a submodule `N` of `M` to `M` is injective.


## Instances

- `IsNoetherianRing.orzechProperty` (defined in `Mathlib/RingTheory/Noetherian/Orzech.lean`) :
  any left-Noetherian ring satisfies the Orzech property.
  This applies in particular to division rings.

- `strongRankCondition_of_orzechProperty` : the Orzech property implies the strong rank condition
  (for non-trivial rings).

- `IsNoetherianRing.strongRankCondition` : every nontrivial left-Noetherian ring satisfies the
  strong rank condition (and so in particular every division ring or field).

- `rankCondition_of_strongRankCondition` : the strong rank condition implies the rank condition.

- `invariantBasisNumber_of_rankCondition` : the rank condition implies the
  invariant basis number property.

- `invariantBasisNumber_of_nontrivial_of_commRing`: a nontrivial commutative ring satisfies
  the invariant basis number property.

More generally, every commutative ring satisfies the Orzech property,
hence the strong rank condition, which is proved in `Mathlib/RingTheory/FiniteType.lean`.
We keep `invariantBasisNumber_of_nontrivial_of_commRing` here since it imports fewer files.


## Counterexamples to converse results

The following examples can be found in the book of Lam [lam_1999]
(see also <https://math.stackexchange.com/questions/4711904>):

- Let `k` be a field, then the free (non-commutative) algebra `k⟨x, y⟩` satisfies
  the rank condition but not the strong rank condition.
- The free (non-commutative) algebra `ℚ⟨a, b, c, d⟩` quotient by the
  two-sided ideal `(ac − 1, bd − 1, ab, cd)` satisfies the invariant basis number property
  but not the rank condition.


## Future work

So far, there is no API at all for the `InvariantBasisNumber` class. There are several natural
ways to formulate that a module `M` is finitely generated and free, for example
`M ≃ₗ[R] (Fin n → R)`, `M ≃ₗ[R] (ι → R)`, where `ι` is a fintype, or providing a basis indexed by
a finite type. There should be lemmas applying the invariant basis number property to each
situation.

The finite version of the invariant basis number property implies the infinite analogue, i.e., that
`(ι →₀ R) ≃ₗ[R] (ι' →₀ R)` implies that `Cardinal.mk ι = Cardinal.mk ι'`. This fact (and its
variants) should be formalized.

## References

* https://en.wikipedia.org/wiki/Invariant_basis_number
* https://mathoverflow.net/a/2574/
* [Lam, T. Y. *Lectures on Modules and Rings*][lam_1999]
* [Orzech, Morris. *Onto endomorphisms are isomorphisms*][orzech1971]
* [Djoković, D. Ž. *Epimorphisms of modules which must be isomorphisms*][djokovic1973]
* [Ribenboim, Paulo.
  *Épimorphismes de modules qui sont nécessairement des isomorphismes*][ribenboim1971]

## Tags

free module, rank, Orzech property, (strong) rank condition, invariant basis number, IBN

-/

@[expose] public section

noncomputable section

open Function

universe u v w

section

variable (R : Type u) [Semiring R]

/-- We say that `R` satisfies the strong rank condition if `(Fin n → R) →ₗ[R] (Fin m → R)` injective
    implies `n ≤ m`. -/
@[mk_iff]
/--
Definition of `StrongRankCondition` / `StrongRankCondition` 的定义

English:
class StrongRankCondition
  parameters: : Prop where
  axioms and operations (1):
    - le_of_fin_injective : forall {n m : Nat} (f : (Fin n -> R) ->ₗ[R] Fin m -> R), Injective f -> n <= m

中文:
类 StrongRankCondition
  参数: : 命题 where
  公理与运算 (1 个):
    - le_of_fin_injective : 对任意 {n m : 自然数} (f : (Fin n -> R) ->ₗ[R] Fin m -> R), Injective f -> n <= m
-/
class StrongRankCondition : Prop where
  /-- Any injective linear map from `Rⁿ` to `Rᵐ` guarantees `n ≤ m`. -/
  le_of_fin_injective : forall {n m : Nat} (f : (Fin n -> R) ->ₗ[R] Fin m -> R), Injective f -> n <= m

/--
theorem `le_of_fin_injective` / 定理 `le_of_fin_injective`

English:
theorem le_of_fin_injective
  given: [StrongRankCondition R] {n m : Nat} (f : (Fin n -> R) ->ₗ[R] Fin m -> R)
  proof: StrongRankCondition.le_of_fin_injective f

中文:
定理 le_of_fin_injective
  条件: [StrongRankCondition R] {n m : 自然数} (f : (Fin n -> R) ->ₗ[R] Fin m -> R)
  证明: StrongRankCondition.le_of_fin_injective f

Depends on / 依赖: StrongRankCondition, StrongRankCondition.le_of_fin_injective, le_of_fin_injective
-/
theorem le_of_fin_injective [StrongRankCondition R] {n m : Nat} (f : (Fin n -> R) ->ₗ[R] Fin m -> R) :
    Injective f -> n <= m :=
  StrongRankCondition.le_of_fin_injective f

/--
theorem `strongRankCondition_iff_succ` / 定理 `strongRankCondition_iff_succ`

English:
theorem strongRankCondition_iff_succ
  proof: by
  refine ⟨fun h n => fun f hf => ?_, fun h => ⟨@fun n m f hf => ?_⟩⟩
  · exact Nat.not_succ_le_self n (le_of_fin_injective R f hf)
  · by_contra H
    exact
      h m (f.comp (Function.ExtendByZero.linearMap R (Fin.castLE (not_le.1 H))))
        (hf.comp (Function.extend_injective (Fin.strictMono

中文:
定理 strongRankCondition_iff_succ
  证明: by
  refine ⟨fun h n => fun f hf => ?_, fun h => ⟨@fun n m f hf => ?_⟩⟩
  · exact Nat.not_succ_le_self n (le_of_fin_injective R f hf)
  · by_contra H
    exact
      h m (f.comp (Function.ExtendByZero.linearMap R (Fin.castLE (not_le.1 H))))
        (hf.comp (Function.extend_injective (Fin.strictMono

Depends on / 依赖: ExtendByZero, Fin.castLE, Fin.strictMono_castLE, Function, Function.ExtendByZero.linearMap, Function.extend_injective, Nat.not_succ_le_self, castLE, extend_injective, f.comp, hf.comp, injective, le_of_fin_injective, linearMap, not_le, not_succ_le_self, strictMono_castLE
-/
theorem strongRankCondition_iff_succ :
    StrongRankCondition R ↔
      forall (n : Nat) (f : (Fin (n + 1) -> R) ->ₗ[R] Fin n -> R), ¬Function.Injective f := by
  refine ⟨fun h n => fun f hf => ?_, fun h => ⟨@fun n m f hf => ?_⟩⟩
  · exact Nat.not_succ_le_self n (le_of_fin_injective R f hf)
  · by_contra H
    exact
      h m (f.comp (Function.ExtendByZero.linearMap R (Fin.castLE (not_le.1 H))))
        (hf.comp (Function.extend_injective (Fin.strictMono_castLE _).injective _))

/-- Any nontrivial ring satisfying Orzech property also satisfies strong rank condition. -/
instance (priority := 100) strongRankCondition_of_orzechProperty
    [Nontrivial R] [OrzechProperty R] : StrongRankCondition R := by
  refine (strongRankCondition_iff_succ R).2 fun n i hi => ?_
  have h : (0 : Fin (n + 1) -> R) = update (0 : Fin (n + 1) -> R) (Fin.last n) 1 := by
    apply OrzechProperty.injective_of_surjective_of_injective i (.funLeft ..) hi
      (Fin.castSucc_injective _).surjective_comp_right
    ext; simp
  simpa using congr_fun h (Fin.last n)

/--
theorem `card_le_of_injective` / 定理 `card_le_of_injective`

English:
theorem card_le_of_injective
  statement: [StrongRankCondition R] {α β : Type*} [Fintype α] [Fintype β]
  proof: by
  let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
  let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
  exact le_of_fin_injective R
    (Q.symm.toLinearMap ∘ₗ f ∘ₗ P) (Q.symm.injective.comp (i.comp P.injective))

中文:
定理 card_le_of_injective
  结论: [StrongRankCondition R] {α β : 类型} [Fintype α] [Fintype β]
  证明: by
  let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
  let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
  exact le_of_fin_injective R
    (Q.symm.toLinearMap ∘ₗ f ∘ₗ P) (Q.symm.injective.comp (i.comp P.injective))

Depends on / 依赖: Fintype, Fintype.equivFin, LinearEquiv, LinearEquiv.funCongrLeft, P.injective, Q.symm.injective.comp, Q.symm.toLinearMap, equivFin, funCongrLeft, i.comp, injective, le_of_fin_injective, toLinearMap
-/
theorem card_le_of_injective [StrongRankCondition R] {α β : Type*} [Fintype α] [Fintype β]
    (f : (α -> R) ->ₗ[R] β -> R) (i : Injective f) : Fintype.card α <= Fintype.card β := by
  let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
  let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
  exact le_of_fin_injective R
    (Q.symm.toLinearMap ∘ₗ f ∘ₗ P) (Q.symm.injective.comp (i.comp P.injective))

/--
theorem `card_le_of_injective'` / 定理 `card_le_of_injective'`

English:
theorem card_le_of_injective'
  statement: [StrongRankCondition R] {α β : Type*} [Fintype α] [Fintype β]
  proof: by
  let P := Finsupp.linearEquivFunOnFinite R R β
  let Q := (Finsupp.linearEquivFunOnFinite R R α).symm
  exact card_le_of_injective R (P.toLinearMap ∘ₗ f ∘ₗ Q) (P.injective.comp (i.comp Q.injective))

中文:
定理 card_le_of_injective'
  结论: [StrongRankCondition R] {α β : 类型} [Fintype α] [Fintype β]
  证明: by
  let P := Finsupp.linearEquivFunOnFinite R R β
  let Q := (Finsupp.linearEquivFunOnFinite R R α).symm
  exact card_le_of_injective R (P.toLinearMap ∘ₗ f ∘ₗ Q) (P.injective.comp (i.comp Q.injective))

Depends on / 依赖: Finsupp, Finsupp.linearEquivFunOnFinite, P.injective.comp, P.toLinearMap, Q.injective, card_le_of_injective, i.comp, injective, linearEquivFunOnFinite, toLinearMap
-/
theorem card_le_of_injective' [StrongRankCondition R] {α β : Type*} [Fintype α] [Fintype β]
    (f : (α ->₀ R) ->ₗ[R] β ->₀ R) (i : Injective f) : Fintype.card α <= Fintype.card β := by
  let P := Finsupp.linearEquivFunOnFinite R R β
  let Q := (Finsupp.linearEquivFunOnFinite R R α).symm
  exact card_le_of_injective R (P.toLinearMap ∘ₗ f ∘ₗ Q) (P.injective.comp (i.comp Q.injective))

/--
Definition of `RankCondition` / `RankCondition` 的定义

English:
class RankCondition
  parameters: : Prop where
  axioms and operations (1):
    - le_of_fin_surjective : forall {n m : Nat} (f : (Fin n -> R) ->ₗ[R] Fin m -> R), Surjective f -> m <= n

中文:
类 RankCondition
  参数: : 命题 where
  公理与运算 (1 个):
    - le_of_fin_surjective : 对任意 {n m : 自然数} (f : (Fin n -> R) ->ₗ[R] Fin m -> R), Surjective f -> m <= n
-/
@[mk_iff] class RankCondition : Prop where
  /-- Any surjective linear map from `Rⁿ` to `Rᵐ` guarantees `m ≤ n`. -/
  le_of_fin_surjective : forall {n m : Nat} (f : (Fin n -> R) ->ₗ[R] Fin m -> R), Surjective f -> m <= n

/--
theorem `le_of_fin_surjective` / 定理 `le_of_fin_surjective`

English:
theorem le_of_fin_surjective
  given: [RankCondition R] {n m : Nat} (f : (Fin n -> R) ->ₗ[R] Fin m -> R)
  proof: RankCondition.le_of_fin_surjective f

中文:
定理 le_of_fin_surjective
  条件: [RankCondition R] {n m : 自然数} (f : (Fin n -> R) ->ₗ[R] Fin m -> R)
  证明: RankCondition.le_of_fin_surjective f

Depends on / 依赖: RankCondition, RankCondition.le_of_fin_surjective, le_of_fin_surjective
-/
theorem le_of_fin_surjective [RankCondition R] {n m : Nat} (f : (Fin n -> R) ->ₗ[R] Fin m -> R) :
    Surjective f -> m <= n :=
  RankCondition.le_of_fin_surjective f

/--
theorem `card_le_of_surjective` / 定理 `card_le_of_surjective`

English:
theorem card_le_of_surjective
  statement: [RankCondition R] {α β : Type*} [Fintype α] [Fintype β]
  proof: by
  let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
  let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
  exact le_of_fin_surjective R
    (Q.symm.toLinearMap ∘ₗ f ∘ₗ P) (Q.symm.surjective.comp (i.comp P.surjective))

中文:
定理 card_le_of_surjective
  结论: [RankCondition R] {α β : 类型} [Fintype α] [Fintype β]
  证明: by
  let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
  let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
  exact le_of_fin_surjective R
    (Q.symm.toLinearMap ∘ₗ f ∘ₗ P) (Q.symm.surjective.comp (i.comp P.surjective))

Depends on / 依赖: Fintype, Fintype.equivFin, LinearEquiv, LinearEquiv.funCongrLeft, P.surjective, Q.symm.surjective.comp, Q.symm.toLinearMap, equivFin, funCongrLeft, i.comp, le_of_fin_surjective, surjective, toLinearMap
-/
theorem card_le_of_surjective [RankCondition R] {α β : Type*} [Fintype α] [Fintype β]
    (f : (α -> R) ->ₗ[R] β -> R) (i : Surjective f) : Fintype.card β <= Fintype.card α := by
  let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
  let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
  exact le_of_fin_surjective R
    (Q.symm.toLinearMap ∘ₗ f ∘ₗ P) (Q.symm.surjective.comp (i.comp P.surjective))

/--
theorem `card_le_of_surjective'` / 定理 `card_le_of_surjective'`

English:
theorem card_le_of_surjective'
  statement: [RankCondition R] {α β : Type*} [Fintype α] [Fintype β]
  proof: by
  let P := Finsupp.linearEquivFunOnFinite R R β
  let Q := (Finsupp.linearEquivFunOnFinite R R α).symm
  exact card_le_of_surjective R (P.toLinearMap ∘ₗ f ∘ₗ Q) (P.surjective.comp (i.comp Q.surjective))

中文:
定理 card_le_of_surjective'
  结论: [RankCondition R] {α β : 类型} [Fintype α] [Fintype β]
  证明: by
  let P := Finsupp.linearEquivFunOnFinite R R β
  let Q := (Finsupp.linearEquivFunOnFinite R R α).symm
  exact card_le_of_surjective R (P.toLinearMap ∘ₗ f ∘ₗ Q) (P.surjective.comp (i.comp Q.surjective))

Depends on / 依赖: Finsupp, Finsupp.linearEquivFunOnFinite, P.surjective.comp, P.toLinearMap, Q.surjective, card_le_of_surjective, i.comp, linearEquivFunOnFinite, surjective, toLinearMap
-/
theorem card_le_of_surjective' [RankCondition R] {α β : Type*} [Fintype α] [Fintype β]
    (f : (α ->₀ R) ->ₗ[R] β ->₀ R) (i : Surjective f) : Fintype.card β <= Fintype.card α := by
  let P := Finsupp.linearEquivFunOnFinite R R β
  let Q := (Finsupp.linearEquivFunOnFinite R R α).symm
  exact card_le_of_surjective R (P.toLinearMap ∘ₗ f ∘ₗ Q) (P.surjective.comp (i.comp Q.surjective))

/--
theorem `Module.Finite.exists_nat_not_surjective` / 定理 `Module.Finite.exists_nat_not_surjective`

English:
theorem Module.Finite.exists_nat_not_surjective
  statement: [RankCondition R] (M) [AddCommMonoid M] [Module R M]
  proof: have ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  ⟨n + 1, fun g hg => by simpa using le_of_fin_surjective R (g ∘ₗ f) (hg.comp hf)⟩

中文:
定理 Module.Finite.exists_nat_not_surjective
  结论: [RankCondition R] (M) [AddCommMonoid M] [Module R M]
  证明: have ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  ⟨n + 1, fun g hg => by simpa using le_of_fin_surjective R (g ∘ₗ f) (hg.comp hf)⟩

Depends on / 依赖: Finite, Module, Module.Finite.exists_fin, exists_fin, hg.comp, le_of_fin_surjective
-/
theorem Module.Finite.exists_nat_not_surjective [RankCondition R] (M) [AddCommMonoid M] [Module R M]
    [Module.Finite R M] : exists n : Nat, forall f : M ->ₗ[R] (Fin n -> R), ¬Surjective f :=
  have ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  ⟨n + 1, fun g hg => by simpa using le_of_fin_surjective R (g ∘ₗ f) (hg.comp hf)⟩

/-- By the universal property for free modules, any surjective map `(Fin n → R) →ₗ[R] (Fin m → R)`
has an injective splitting `(Fin m → R) →ₗ[R] (Fin n → R)`
from which the strong rank condition gives the necessary inequality for the rank condition.
-/
instance (priority := 100) rankCondition_of_strongRankCondition [StrongRankCondition R] :
    RankCondition R where
  le_of_fin_surjective f s :=
    le_of_fin_injective R _ (f.splittingOfFunOnFintypeSurjective_injective s)

/--
Definition of `InvariantBasisNumber` / `InvariantBasisNumber` 的定义

English:
class InvariantBasisNumber
  parameters: : Prop where
  axioms and operations (1):
    - eq_of_fin_equiv : forall {n m : Nat}, ((Fin n -> R) ≃ₗ[R] Fin m -> R) -> n = m

中文:
类 InvariantBasisNumber
  参数: : 命题 where
  公理与运算 (1 个):
    - eq_of_fin_equiv : 对任意 {n m : 自然数}, ((Fin n -> R) ≃ₗ[R] Fin m -> R) -> n = m
-/
@[mk_iff] class InvariantBasisNumber : Prop where
  /-- Any linear equiv between `Rⁿ` and `Rᵐ` guarantees `m = n`. -/
  eq_of_fin_equiv : forall {n m : Nat}, ((Fin n -> R) ≃ₗ[R] Fin m -> R) -> n = m

instance (priority := 100) invariantBasisNumber_of_rankCondition [RankCondition R] :
    InvariantBasisNumber R where
  eq_of_fin_equiv e := le_antisymm (le_of_fin_surjective R e.symm.toLinearMap e.symm.surjective)
    (le_of_fin_surjective R e.toLinearMap e.surjective)

/--
theorem `strongRankCondition_iff_forall_not_injective` / 定理 `strongRankCondition_iff_forall_not_injective`

English:
theorem strongRankCondition_iff_forall_not_injective
  proof: by
  rw [strongRankCondition_iff_succ]; rw [← not_iff_not]; push Not
  constructor <;> refine fun ⟨n, f, inj⟩ => ⟨n, ?_⟩
  · exact f.exists_finsupp_nat_of_fin_fun_injective inj
  · exact ⟨f ∘ₗ Finsupp.lmapDomain R R (↑) ∘ₗ (Finsupp.linearEquivFunOnFinite ..).symm.toLinearMap,
inj.comp by simpa using

中文:
定理 strongRankCondition_iff_forall_not_injective
  证明: by
  rw [strongRankCondition_iff_succ]; rw [← not_iff_not]; push Not
  constructor <;> refine fun ⟨n, f, inj⟩ => ⟨n, ?_⟩
  · exact f.exists_finsupp_nat_of_fin_fun_injective inj
  · exact ⟨f ∘ₗ Finsupp.lmapDomain R R (↑) ∘ₗ (Finsupp.linearEquivFunOnFinite ..).symm.toLinearMap,
inj.comp by simpa using

Depends on / 依赖: Fin.val_injective, Finsupp, Finsupp.linearEquivFunOnFinite, Finsupp.lmapDomain, Finsupp.mapDomain_injective, exists_finsupp_nat_of_fin_fun_injective, f.exists_finsupp_nat_of_fin_fun_injective, inj.comp, linearEquivFunOnFinite, lmapDomain, mapDomain_injective, not_iff_not, strongRankCondition_iff_succ, symm.toLinearMap, toLinearMap, val_injective
-/
theorem strongRankCondition_iff_forall_not_injective :
    StrongRankCondition R ↔ forall n (f : (Nat ->₀ R) ->ₗ[R] Fin n -> R), ¬ Injective f := by
  rw [strongRankCondition_iff_succ]; rw [← not_iff_not]; push Not
  constructor <;> refine fun ⟨n, f, inj⟩ => ⟨n, ?_⟩
  · exact f.exists_finsupp_nat_of_fin_fun_injective inj
  · exact ⟨f ∘ₗ Finsupp.lmapDomain R R (↑) ∘ₗ (Finsupp.linearEquivFunOnFinite ..).symm.toLinearMap,
inj.comp by simpa using! Finsupp.mapDomain_injective Fin.val_injective⟩

end

section

variable (R : Type u) [Semiring R] [InvariantBasisNumber R]

/--
theorem `eq_of_fin_equiv` / 定理 `eq_of_fin_equiv`

English:
theorem eq_of_fin_equiv
  given: {n m : Nat}
  statement: ((Fin n -> R) ≃ₗ[R] Fin m -> R) -> n = m
  proof: InvariantBasisNumber.eq_of_fin_equiv

中文:
定理 eq_of_fin_equiv
  条件: {n m : 自然数}
  结论: ((Fin n -> R) ≃ₗ[R] Fin m -> R) -> n = m
  证明: InvariantBasisNumber.eq_of_fin_equiv

Depends on / 依赖: InvariantBasisNumber, InvariantBasisNumber.eq_of_fin_equiv, eq_of_fin_equiv
-/
theorem eq_of_fin_equiv {n m : Nat} : ((Fin n -> R) ≃ₗ[R] Fin m -> R) -> n = m :=
  InvariantBasisNumber.eq_of_fin_equiv

/--
theorem `card_eq_of_linearEquiv` / 定理 `card_eq_of_linearEquiv`

English:
theorem card_eq_of_linearEquiv
  given: {α β : Type*} [Fintype α] [Fintype β] (f : (α -> R) ≃ₗ[R] β -> R)
  proof: eq_of_fin_equiv R
    (.funCongrLeft R R (Fintype.equivFin α) ≪≫ₗ f ≪≫ₗ
      .symm (.funCongrLeft R R (Fintype.equivFin β)))

中文:
定理 card_eq_of_linearEquiv
  条件: {α β : 类型} [Fintype α] [Fintype β] (f : (α -> R) ≃ₗ[R] β -> R)
  证明: eq_of_fin_equiv R
    (.funCongrLeft R R (Fintype.equivFin α) ≪≫ₗ f ≪≫ₗ
      .symm (.funCongrLeft R R (Fintype.equivFin β)))

Depends on / 依赖: Fintype, Fintype.equivFin, eq_of_fin_equiv, equivFin, funCongrLeft
-/
theorem card_eq_of_linearEquiv {α β : Type*} [Fintype α] [Fintype β] (f : (α -> R) ≃ₗ[R] β -> R) :
    Fintype.card α = Fintype.card β :=
  eq_of_fin_equiv R
    (.funCongrLeft R R (Fintype.equivFin α) ≪≫ₗ f ≪≫ₗ
      .symm (.funCongrLeft R R (Fintype.equivFin β)))

/--
theorem `nontrivial_of_invariantBasisNumber` / 定理 `nontrivial_of_invariantBasisNumber`

English:
theorem nontrivial_of_invariantBasisNumber
  statement: Nontrivial R
  proof: by
  by_contra! h
  exact zero_ne_one (eq_of_fin_equiv R <| .ofSubsingleton ..)

中文:
定理 nontrivial_of_invariantBasisNumber
  结论: Nontrivial R
  证明: by
  by_contra! h
  exact zero_ne_one (eq_of_fin_equiv R <| .ofSubsingleton ..)

Depends on / 依赖: eq_of_fin_equiv, ofSubsingleton, zero_ne_one
-/
theorem nontrivial_of_invariantBasisNumber : Nontrivial R := by
  by_contra! h
  exact zero_ne_one (eq_of_fin_equiv R <| .ofSubsingleton ..)

end

section

variable (R : Type u) [Ring R] [Nontrivial R] [IsNoetherianRing R]

/-- Any nontrivial Noetherian ring satisfies the strong rank condition,
    since it satisfies Orzech property. -/
instance (priority := 100) IsNoetherianRing.strongRankCondition : StrongRankCondition R :=
  inferInstance

end

/-!
  We want to show that nontrivial commutative rings have invariant basis number. The idea is to
  take a maximal ideal `I` of `R` and use an isomorphism `R^n ≃ R^m` of `R` modules to produce an
  isomorphism `(R/I)^n ≃ (R/I)^m` of `R/I`-modules, which will imply `n = m` since `R/I` is a field
  and we know that fields have invariant basis number.

  We construct the isomorphism in two steps:
  1. We construct the ring `R^n/I^n`, show that it is an `R/I`-module and show that there is an
     isomorphism of `R/I`-modules `R^n/I^n ≃ (R/I)^n`. This isomorphism is called
    `Ideal.piQuotEquiv` and is located in the file `Mathlib/RingTheory/Ideal/Quotient/Basic.lean`.
  2. We construct an isomorphism of `R/I`-modules `R^n/I^n ≃ R^m/I^m` using the isomorphism
     `R^n ≃ R^m`.
-/


section

variable {R : Type u} [CommRing R] (I : Ideal R) {ι : Type v} [Fintype ι] {ι' : Type w}

/--
Definition of `induced_map` / `induced_map` 的定义

English:
definition induced_map
  signature: (I : Ideal R) (e : (ι -> R) ->ₗ[R] ι' -> R)
  body: fun x =>
  Quotient.liftOn' x (fun y => Ideal.Quotient.mk _ (e y))
    fun a b hab => Ideal.Quotient.eq.2 fun h => by
      rw [Submodule.quotientRel_def] at hab
      rw [← map_sub]
      exact Ideal.map_pi _ _ hab e h

中文:
定义 induced_map
  签名: (I : Ideal R) (e : (ι -> R) ->ₗ[R] ι' -> R)
  定义体: fun x =>
  Quotient.liftOn' x (fun y => Ideal.Quotient.mk _ (e y))
    fun a b hab => Ideal.Quotient.eq.2 fun h => by
      rw [Submodule.quotientRel_def] at hab
      rw [← map_sub]
      exact Ideal.map_pi _ _ hab e h
-/
private def induced_map (I : Ideal R) (e : (ι -> R) ->ₗ[R] ι' -> R) :
    (ι -> R) ⧸ Ideal.pi (fun _ => I) -> (ι' -> R) ⧸ Ideal.pi fun _ => I := fun x =>
  Quotient.liftOn' x (fun y => Ideal.Quotient.mk _ (e y))
    fun a b hab => Ideal.Quotient.eq.2 fun h => by
      rw [Submodule.quotientRel_def] at hab
      rw [← map_sub]
      exact Ideal.map_pi _ _ hab e h

/--
Definition of `inducedEquiv` / `inducedEquiv` 的定义

English:
definition inducedEquiv
  signature: [Fintype ι'] (I : Ideal R) (e : (ι -> R) ≃ₗ[R] ι' -> R)
  body: induced_map I e
  invFun := induced_map I e.symm
  map_add' := by rintro ⟨a⟩ ⟨b⟩; exact congr_arg _ (map_add ..)
  map_smul' := by rintro ⟨a⟩ ⟨b⟩; exact congr_arg _ (map_smul ..)
  left_inv := by rintro ⟨a⟩; exact congr_arg _ (e.left_inv ..)
  right_inv := by rintro ⟨a⟩; exact congr_arg _ (e.right_i

中文:
定义 inducedEquiv
  签名: [Fintype ι'] (I : Ideal R) (e : (ι -> R) ≃ₗ[R] ι' -> R)
  定义体: induced_map I e
  invFun := induced_map I e.symm
  map_add' := by rintro ⟨a⟩ ⟨b⟩; exact congr_arg _ (map_add ..)
  map_smul' := by rintro ⟨a⟩ ⟨b⟩; exact congr_arg _ (map_smul ..)
  left_inv := by rintro ⟨a⟩; exact congr_arg _ (e.left_inv ..)
  right_inv := by rintro ⟨a⟩; exact congr_arg _ (e.right_i
-/
private def inducedEquiv [Fintype ι'] (I : Ideal R) (e : (ι -> R) ≃ₗ[R] ι' -> R) :
    ((ι -> R) ⧸ Ideal.pi fun _ => I) ≃ₗ[R ⧸ I] (ι' -> R) ⧸ Ideal.pi fun _ => I where
  toFun := induced_map I e
  invFun := induced_map I e.symm
  map_add' := by rintro ⟨a⟩ ⟨b⟩; exact congr_arg _ (map_add ..)
  map_smul' := by rintro ⟨a⟩ ⟨b⟩; exact congr_arg _ (map_smul ..)
  left_inv := by rintro ⟨a⟩; exact congr_arg _ (e.left_inv ..)
  right_inv := by rintro ⟨a⟩; exact congr_arg _ (e.right_inv ..)

end

section

attribute [local instance] Ideal.Quotient.field

/--
Nontrivial commutative rings satisfy the invariant basis number property.

There are two stronger results in mathlib:
1. `CommRing.orzechProperty` in `Mathlib.RingTheory.FiniteType`,
    which says that any commutative ring satisfies the Orzech property, and hence
    (by `strongRankCondition_of_orzechProperty`) that nontrivial commutative rings satisfy
    the strong rank condition. A shortcut instance `commRing_strongRankCondition` is also provided.
2. `rankCondition_of_nontrivial_of_commSemiring` in
    `Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber`, which says that
    any nontrivial commutative semiring satisfies the rank condition.

We prove this instance here anyway to reduce the required imports.
-/
instance (priority := 100) invariantBasisNumber_of_nontrivial_of_commRing {R : Type u} [CommRing R]
    [Nontrivial R] : InvariantBasisNumber R :=
  ⟨fun e =>
    let ⟨I, _hI⟩ := Ideal.exists_maximal R
    eq_of_fin_equiv (R ⧸ I)
      ((Ideal.piQuotEquiv _ _).symm ≪≫ₗ inducedEquiv _ e ≪≫ₗ Ideal.piQuotEquiv _ _)⟩

end
