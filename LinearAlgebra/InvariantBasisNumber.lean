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
/-
**StrongRankCondition** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [Semiring R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `R` satisfies the strong rank condition if `(Fin n → R) →ₗ[R] (Fin m
 → R)` injective
    implies `n ≤ m`.
-/
class StrongRankCondition : Prop where
  /-- Any injective linear map from `Rⁿ` to `Rᵐ` guarantees `n ≤ m`. -/
  le_of_fin_injective : ∀ {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R), Injective f → n ≤ m
/-
**le_of_fin_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_fin_injective [StrongRankCondition R] {n m : Nat} (f : (Fin n -> R) 
->ₗ[R] Fin m -> R) : Injective f -> n <= m
参数：f : (Fin n -> R) ->ₗ[R] Fin m -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrongRankCondition.le_of_fin_injective`：∀ {R : Type u} {inst : Semiring
 R} [self : StrongRankCondition R] {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R), 
  Function.Injective ⇑f → n ≤…
-/
theorem le_of_fin_injective [StrongRankCondition R] {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R) :
    Injective f → n ≤ m :=
  StrongRankCondition.le_of_fin_injective f

/-- A ring satisfies the strong rank condition if and only if, for all `n : ℕ`, any linear map
`(Fin (n + 1) → R) →ₗ[R] (Fin n → R)` is not injective. -/
/-
**strongRankCondition_iff_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strongRankCondition_iff_succ : StrongRankCondition R ↔ forall (n : Nat) (f
 : (Fin (n + 1) -> R) ->ₗ[R] Fin n -> R), ¬Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_succ_le_self`：∀ (n : ℕ), ¬n.succ ≤ n
· 使用定理 `le_of_fin_injective`：le_of_fin_injective [StrongRankCondition R] {n m : 
Nat} (f : (Fin n -> R) ->ₗ[R] Fin m -> R) : Injective f -> n <= m
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Function.extend_injective`：extend_injective (hf : Injective f) (e' : β -
> γ) : Injective fun g => extend f g e'
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `Fin.strictMono_castLE`：strictMono_castLE (h : n <= m) : StrictMono (cast
LE h : Fin n -> Fin m)

--- 原说明 ---
A ring satisfies the strong rank condition if and only if, for all `n : ℕ`, any 
linear map
`(Fin (n + 1) → R) →ₗ[R] (Fin n → R)` is not injective.
-/
theorem strongRankCondition_iff_succ :
    StrongRankCondition R ↔
      ∀ (n : ℕ) (f : (Fin (n + 1) → R) →ₗ[R] Fin n → R), ¬Function.Injective f := by
  refine ⟨fun h n => fun f hf => ?_, fun h => ⟨@fun n m f hf => ?_⟩⟩
  · exact Nat.not_succ_le_self n (le_of_fin_injective R f hf)
  · by_contra H
    exact
      h m (f.comp (Function.ExtendByZero.linearMap R (Fin.castLE (not_le.1 H))))
        (hf.comp (Function.extend_injective (Fin.strictMono_castLE _).injective _))

/-- Any nontrivial ring satisfying Orzech property also satisfies strong rank condition. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any nontrivial ring satisfying Orzech property also satisfies strong rank condit
ion.
-/
instance (priority := 100) strongRankCondition_of_orzechProperty
    [Nontrivial R] [OrzechProperty R] : StrongRankCondition R := by
  refine (strongRankCondition_iff_succ R).2 fun n i hi ↦ ?_
  have h : (0 : Fin (n + 1) → R) = update (0 : Fin (n + 1) → R) (Fin.last n) 1 := by
    apply OrzechProperty.injective_of_surjective_of_injective i (.funLeft ..) hi
      (Fin.castSucc_injective _).surjective_comp_right
    ext; simp
  simpa using congr_fun h (Fin.last n)
/-
**card_le_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_le_of_injective [StrongRankCondition R] {α β : Type*} [Fintype α] [Fi
ntype β] (f : (α -> R) ->ₗ[R] β -> R) (i : Injective f) : Fintype.card α <= Fint
ype.card β
参数：f : (α -> R) ->ₗ[R] β -> R；i : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_fin_injective`：le_of_fin_injective [StrongRankCondition R] {n m : 
Nat} (f : (Fin n -> R) ->ₗ[R] Fin m -> R) : Injective f -> n <= m
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem card_le_of_injective [StrongRankCondition R] {α β : Type*} [Fintype α] [Fintype β]
    (f : (α → R) →ₗ[R] β → R) (i : Injective f) : Fintype.card α ≤ Fintype.card β := by
  let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
  let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
  exact le_of_fin_injective R
    (Q.symm.toLinearMap ∘ₗ f ∘ₗ P) (Q.symm.injective.comp (i.comp P.injective))
/-
**card_le_of_injective'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_le_of_injective' [StrongRankCondition R] {α β : Type*} [Fintype α] [F
intype β] (f : (α ->₀ R) ->ₗ[R] β ->₀ R) (i : Injective f) : Fintype.card α <= F
intype.card β
参数：f : (α ->₀ R) ->ₗ[R] β ->₀ R；i : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `card_le_of_injective`：card_le_of_injective [StrongRankCondition R] {α β 
: Type*} [Fintype α] [Fintype β] (f : (α -> R) ->ₗ[R] β -> R) (i : Injective f) 
: Fintype.…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem card_le_of_injective' [StrongRankCondition R] {α β : Type*} [Fintype α] [Fintype β]
    (f : (α →₀ R) →ₗ[R] β →₀ R) (i : Injective f) : Fintype.card α ≤ Fintype.card β := by
  let P := Finsupp.linearEquivFunOnFinite R R β
  let Q := (Finsupp.linearEquivFunOnFinite R R α).symm
  exact card_le_of_injective R (P.toLinearMap ∘ₗ f ∘ₗ Q) (P.injective.comp (i.comp Q.injective))

/-- We say that `R` satisfies the rank condition if `(Fin n → R) →ₗ[R] (Fin m → R)` surjective
    implies `m ≤ n`. -/
/-
**RankCondition** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [Semiring R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `R` satisfies the rank condition if `(Fin n → R) →ₗ[R] (Fin m → R)` 
surjective
    implies `m ≤ n`.
-/
@[mk_iff] class RankCondition : Prop where
  /-- Any surjective linear map from `Rⁿ` to `Rᵐ` guarantees `m ≤ n`. -/
  le_of_fin_surjective : ∀ {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R), Surjective f → m ≤ n
/-
**le_of_fin_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_fin_surjective [RankCondition R] {n m : Nat} (f : (Fin n -> R) ->ₗ[R
] Fin m -> R) : Surjective f -> m <= n
参数：f : (Fin n -> R) ->ₗ[R] Fin m -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RankCondition.le_of_fin_surjective`：∀ {R : Type u} {inst : Semiring R} [
self : RankCondition R] {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R),   Function.
Surjective ⇑f → m ≤ n
-/
theorem le_of_fin_surjective [RankCondition R] {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R) :
    Surjective f → m ≤ n :=
  RankCondition.le_of_fin_surjective f
/-
**card_le_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_le_of_surjective [RankCondition R] {α β : Type*} [Fintype α] [Fintype
 β] (f : (α -> R) ->ₗ[R] β -> R) (i : Surjective f) : Fintype.card β <= Fintype.
card α
参数：f : (α -> R) ->ₗ[R] β -> R；i : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_fin_surjective`：le_of_fin_surjective [RankCondition R] {n m : Nat}
 (f : (Fin n -> R) ->ₗ[R] Fin m -> R) : Surjective f -> m <= n
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
-/
theorem card_le_of_surjective [RankCondition R] {α β : Type*} [Fintype α] [Fintype β]
    (f : (α → R) →ₗ[R] β → R) (i : Surjective f) : Fintype.card β ≤ Fintype.card α := by
  let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
  let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
  exact le_of_fin_surjective R
    (Q.symm.toLinearMap ∘ₗ f ∘ₗ P) (Q.symm.surjective.comp (i.comp P.surjective))
/-
**card_le_of_surjective'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_le_of_surjective' [RankCondition R] {α β : Type*} [Fintype α] [Fintyp
e β] (f : (α ->₀ R) ->ₗ[R] β ->₀ R) (i : Surjective f) : Fintype.card β <= Finty
pe.card α
参数：f : (α ->₀ R) ->ₗ[R] β ->₀ R；i : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `card_le_of_surjective`：card_le_of_surjective [RankCondition R] {α β : Ty
pe*} [Fintype α] [Fintype β] (f : (α -> R) ->ₗ[R] β -> R) (i : Surjective f) : F
intype.card…
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
-/
theorem card_le_of_surjective' [RankCondition R] {α β : Type*} [Fintype α] [Fintype β]
    (f : (α →₀ R) →ₗ[R] β →₀ R) (i : Surjective f) : Fintype.card β ≤ Fintype.card α := by
  let P := Finsupp.linearEquivFunOnFinite R R β
  let Q := (Finsupp.linearEquivFunOnFinite R R α).symm
  exact card_le_of_surjective R (P.toLinearMap ∘ₗ f ∘ₗ Q) (P.surjective.comp (i.comp Q.surjective))
/-
**Module.Finite.exists_nat_not_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Finite.exists_nat_not_surjective [RankCondition R] (M) [AddCommMono
id M] [Module R M] [Module.Finite R M] : exists n : Nat, forall f : M ->ₗ[R] (Fi
n n -> R), ¬Surjective f
参数：M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Finite.exists_fin'`：exists_fin' [Module.Finite R M] : exists (n :
 Nat) (f : (Fin n -> R) ->ₗ[R] M), Surjective f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_of_fin_surjective`：le_of_fin_surjective [RankCondition R] {n m : Nat}
 (f : (Fin n -> R) ->ₗ[R] Fin m -> R) : Surjective f -> m <= n
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
-/
theorem Module.Finite.exists_nat_not_surjective [RankCondition R] (M) [AddCommMonoid M] [Module R M]
    [Module.Finite R M] : ∃ n : ℕ, ∀ f : M →ₗ[R] (Fin n → R), ¬Surjective f :=
  have ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  ⟨n + 1, fun g hg ↦ by simpa using le_of_fin_surjective R (g ∘ₗ f) (hg.comp hf)⟩

/-- By the universal property for free modules, any surjective map `(Fin n → R) →ₗ[R] (Fin m → R)`
has an injective splitting `(Fin m → R) →ₗ[R] (Fin n → R)`
from which the strong rank condition gives the necessary inequality for the rank condition.
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
By the universal property for free modules, any surjective map `(Fin n → R) →ₗ[R
] (Fin m → R)`
has an injective splitting `(Fin m → R) →ₗ[R] (Fin n → R)`
from which the strong rank condition gives the necessary inequality for the rank
 condition.
-/
instance (priority := 100) rankCondition_of_strongRankCondition [StrongRankCondition R] :
    RankCondition R where
  le_of_fin_surjective f s :=
    le_of_fin_injective R _ (f.splittingOfFunOnFintypeSurjective_injective s)

/-- We say that `R` has the invariant basis number property if `(Fin n → R) ≃ₗ[R] (Fin m → R)`
    implies `n = m`. This gives rise to a well-defined notion of rank of a finitely generated free
    module. -/
/-
**InvariantBasisNumber** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [Semiring R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `R` has the invariant basis number property if `(Fin n → R) ≃ₗ[R] (F
in m → R)`
    implies `n = m`. This gives rise to a well-defined notion of rank of a finit
ely generated free
    module.
-/
@[mk_iff] class InvariantBasisNumber : Prop where
  /-- Any linear equiv between `Rⁿ` and `Rᵐ` guarantees `m = n`. -/
  eq_of_fin_equiv : ∀ {n m : ℕ}, ((Fin n → R) ≃ₗ[R] Fin m → R) → n = m
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) invariantBasisNumber_of_rankCondition [RankCondition R] :
    InvariantBasisNumber R where
  eq_of_fin_equiv e := le_antisymm (le_of_fin_surjective R e.symm.toLinearMap e.symm.surjective)
    (le_of_fin_surjective R e.toLinearMap e.surjective)

/-- A semiring `R` satisfies the strong rank condition, iff we cannot embed `R^(ℕ)` in some `Rⁿ`. -/
/-
**strongRankCondition_iff_forall_not_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strongRankCondition_iff_forall_not_injective : StrongRankCondition R ↔ for
all n (f : (Nat ->₀ R) ->ₗ[R] Fin n -> R), ¬ Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `strongRankCondition_iff_succ`：strongRankCondition_iff_succ : StrongRankC
ondition R ↔ forall (n : Nat) (f : (Fin (n + 1) -> R) ->ₗ[R] Fin n -> R), ¬Funct
ion.Injective f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.exists_finsupp_nat_of_fin_fun_injective`：exists_finsupp_nat_of
_fin_fun_injective {n : Nat} {f : (Fin (n + 1) -> P) ->ₗ[R] Fin n -> P} (inj : I
njective f) : exists g : (Nat ->₀ P) ->…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Finsupp.mapDomain_injective`：mapDomain_injective {f : α -> β} (hf : Func
tion.Injective f) : Function.Injective (mapDomain f : (α ->₀ M) -> β ->₀ M)
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)

--- 原说明 ---
A semiring `R` satisfies the strong rank condition, iff we cannot embed `R^(ℕ)` 
in some `Rⁿ`.
-/
theorem strongRankCondition_iff_forall_not_injective :
    StrongRankCondition R ↔ ∀ n (f : (ℕ →₀ R) →ₗ[R] Fin n → R), ¬ Injective f := by
  rw [strongRankCondition_iff_succ, ← not_iff_not]; push Not
  constructor <;> refine fun ⟨n, f, inj⟩ ↦ ⟨n, ?_⟩
  · exact f.exists_finsupp_nat_of_fin_fun_injective inj
  · exact ⟨f ∘ₗ Finsupp.lmapDomain R R (↑) ∘ₗ (Finsupp.linearEquivFunOnFinite ..).symm.toLinearMap,
      inj.comp <| by simpa using! Finsupp.mapDomain_injective Fin.val_injective⟩

end

section

variable (R : Type u) [Semiring R] [InvariantBasisNumber R]

/-
**eq_of_fin_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_fin_equiv {n m : Nat} : ((Fin n -> R) ≃ₗ[R] Fin m -> R) -> n = m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvariantBasisNumber.eq_of_fin_equiv`：∀ {R : Type u} {inst : Semiring R}
 [self : InvariantBasisNumber R] {n m : ℕ} (a : (Fin n → R) ≃ₗ[R] Fin m → R), n 
= m
-/
theorem eq_of_fin_equiv {n m : ℕ} : ((Fin n → R) ≃ₗ[R] Fin m → R) → n = m :=
  InvariantBasisNumber.eq_of_fin_equiv
/-
**card_eq_of_linearEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_eq_of_linearEquiv {α β : Type*} [Fintype α] [Fintype β] (f : (α -> R)
 ≃ₗ[R] β -> R) : Fintype.card α = Fintype.card β
参数：f : (α -> R) ≃ₗ[R] β -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_fin_equiv`：eq_of_fin_equiv {n m : Nat} : ((Fin n -> R) ≃ₗ[R] Fin m
 -> R) -> n = m
-/
theorem card_eq_of_linearEquiv {α β : Type*} [Fintype α] [Fintype β] (f : (α → R) ≃ₗ[R] β → R) :
    Fintype.card α = Fintype.card β :=
  eq_of_fin_equiv R
    (.funCongrLeft R R (Fintype.equivFin α) ≪≫ₗ f ≪≫ₗ
      .symm (.funCongrLeft R R (Fintype.equivFin β)))
/-
**nontrivial_of_invariantBasisNumber** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nontrivial_of_invariantBasisNumber : Nontrivial R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_fin_equiv`：eq_of_fin_equiv {n m : Nat} : ((Fin n -> R) ≃ₗ[R] Fin m
 -> R) -> n = m
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
-/
theorem nontrivial_of_invariantBasisNumber : Nontrivial R := by
  by_contra! h
  exact zero_ne_one (eq_of_fin_equiv R <| .ofSubsingleton ..)

end

section

variable (R : Type u) [Ring R] [Nontrivial R] [IsNoetherianRing R]

/-- Any nontrivial Noetherian ring satisfies the strong rank condition,
    since it satisfies Orzech property. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any nontrivial Noetherian ring satisfies the strong rank condition,
    since it satisfies Orzech property.
-/
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

/-- An `R`-linear map `R^n → R^m` induces a function `R^n/I^n → R^m/I^m`. -/
/-
**induced_map** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-linear map `R^n → R^m` induces a function `R^n/I^n → R^m/I^m`.
-/
private def induced_map (I : Ideal R) (e : (ι → R) →ₗ[R] ι' → R) :
    (ι → R) ⧸ Ideal.pi (fun _ ↦ I) → (ι' → R) ⧸ Ideal.pi fun _ ↦ I := fun x =>
  Quotient.liftOn' x (fun y => Ideal.Quotient.mk _ (e y))
    fun a b hab => Ideal.Quotient.eq.2 fun h => by
      rw [Submodule.quotientRel_def] at hab
      rw [← map_sub]
      exact Ideal.map_pi _ _ hab e h

/-- An isomorphism of `R`-modules `R^n ≃ R^m` induces an isomorphism of `R/I`-modules
    `R^n/I^n ≃ R^m/I^m`. -/
/-
**inducedEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of `R`-modules `R^n ≃ R^m` induces an isomorphism of `R/I`-module
s
    `R^n/I^n ≃ R^m/I^m`.
-/
private def inducedEquiv [Fintype ι'] (I : Ideal R) (e : (ι → R) ≃ₗ[R] ι' → R) :
    ((ι → R) ⧸ Ideal.pi fun _ ↦ I) ≃ₗ[R ⧸ I] (ι' → R) ⧸ Ideal.pi fun _ ↦ I where
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
1.  `CommRing.orzechProperty` in `Mathlib.RingTheory.FiniteType`,
    which says that any commutative ring satisfies the Orzech property, and hence
    (by `strongRankCondition_of_orzechProperty`) that nontrivial commutative rings satisfy
    the strong rank condition. A shortcut instance `commRing_strongRankCondition` is also provided.
2.  `rankCondition_of_nontrivial_of_commSemiring` in
    `Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber`, which says that
    any nontrivial commutative semiring satisfies the rank condition.

We prove this instance here anyway to reduce the required imports.
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Nontrivial commutative rings satisfy the invariant basis number property.

There are two stronger results in mathlib:
1.  `CommRing.orzechProperty` in `Mathlib.RingTheory.FiniteType`,
    which says that any commutative ring satisfies the Orzech property, and henc
e
    (by `strongRankCondition_of_orzechProperty`) that nontrivial commutative rin
gs satisfy
    the strong rank condition. A shortcut instance `commRing_strongRankCondition
` is also provided.
2.  `rankCondition_of_nontrivial_of_commSemiring` in
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

