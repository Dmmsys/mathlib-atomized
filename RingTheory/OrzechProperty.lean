/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!

# Orzech property of rings

In this file we define the following property of rings:

- `OrzechProperty R` is a type class stating that `R` satisfies the following property:
  for any finitely generated `R`-module `M`, any surjective homomorphism `f : N → M`
  from a submodule `N` of `M` to `M` is injective.
  It was introduced in papers by Orzech [orzech1971], Djoković [djokovic1973] and
  Ribenboim [ribenboim1971], under the names `Π`-ring or `Π₁`-ring.
  It implies the strong rank condition (that is, the existence of an injective linear map
  `(Fin n → R) →ₗ[R] (Fin m → R)` implies `n ≤ m`)
  if the ring is nontrivial (see `Mathlib/LinearAlgebra/InvariantBasisNumber.lean`).

It's proved in the above papers that

- a left-Noetherian ring (not necessarily commutative) satisfies the `OrzechProperty`,
  which in particular includes the division ring case
  (see `Mathlib/RingTheory/Noetherian/Orzech.lean`);
- a commutative ring satisfies the `OrzechProperty`
  (see `Mathlib/RingTheory/FiniteType.lean`).

## References

* [Orzech, Morris. *Onto endomorphisms are isomorphisms*][orzech1971]
* [Djoković, D. Ž. *Epimorphisms of modules which must be isomorphisms*][djokovic1973]
* [Ribenboim, Paulo.
  *Épimorphismes de modules qui sont nécessairement des isomorphismes*][ribenboim1971]

## Tags

free module, rank, Orzech property, (strong) rank condition, invariant basis number, IBN

-/

public section

universe u v w

open Function

variable (R : Type u) [Semiring R]

/-- A ring `R` satisfies the Orzech property, if for any finitely generated `R`-module `M`,
any surjective homomorphism `f : N → M` from a submodule `N` of `M` to `M` is injective.

NOTE: In the definition we need to assume that `M` has the same universe level as `R`, but it
in fact implies the universe polymorphic versions
`OrzechProperty.injective_of_surjective_of_injective`
and `OrzechProperty.injective_of_surjective_of_submodule`. -/
@[mk_iff]
/-
**OrzechProperty** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [Semiring R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring `R` satisfies the Orzech property, if for any finitely generated `R`-modu
le `M`,
any surjective homomorphism `f : N → M` from a submodule `N` of `M` to `M` is in
jective.

NOTE: In the definition we need to assume that `M` has the same universe level a
s `R`, but it
in fact implies the universe polymorphic versions
`OrzechProperty.injective_of_surjective_of_injective`
and `OrzechProperty.injective_of_surjective_of_submodule`.
-/
class OrzechProperty : Prop where
  injective_of_surjective_of_submodule' : ∀ {M : Type u} [AddCommMonoid M] [Module R M]
    [Module.Finite R M] {N : Submodule R M} (f : N →ₗ[R] M), Surjective f → Injective f

namespace OrzechProperty

/-
**OrzechProperty.** 是 Mathlib 中的一个实例，位于命名空间 `OrzechProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite R] : OrzechProperty R where
  injective_of_surjective_of_submodule' {M} _ _ _ {N} _f hf :=
    have : Finite M := Module.finite_of_finite R
    have ⟨_g, hg⟩ := N.subtype_injective.hasLeftInverse
    .of_comp (hg.surjective.comp hf).bijective_of_finite.1

variable {R}

variable [OrzechProperty R] {M : Type v} [AddCommMonoid M] [Module R M] [Module.Finite R M]
/-
**OrzechProperty.injective_of_surjective_of_injective** 是 Mathlib 中的一个定理，位于命名空间 
`OrzechProperty`。
形式化陈述：injective_of_surjective_of_injective {N : Type w} [AddCommMonoid N] [Modul
e R N] (i f : N ->ₗ[R] M) (hi : Injective i) (hf : Surjective f) : Injective f
参数：i f : N ->ₗ[R] M；hi : Injective i；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Finite.exists_fin'`：exists_fin' [Module.Finite R M] : exists (n :
 Nat) (f : (Fin n -> R) ->ₗ[R] M), Surjective f
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OrzechProperty.injective_of_surjective_of_submodule'`：∀ {R : Type u} {in
st : Semiring R} [self : OrzechProperty R] {M : Type u} [inst_1 : AddCommMonoid 
M]   [inst_2 : _root_.Module R M] [Module.…
-/
theorem injective_of_surjective_of_injective
    {N : Type w} [AddCommMonoid N] [Module R N]
    (i f : N →ₗ[R] M) (hi : Injective i) (hf : Surjective f) : Injective f := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R M
  have := small_of_surjective hg
  let := Equiv.addCommMonoid (equivShrink M).symm
  let := Equiv.module R (equivShrink M).symm
  let j : Shrink.{u} M ≃ₗ[R] M := Equiv.linearEquiv R (equivShrink M).symm
  have := Module.Finite.equiv j.symm
  let i' := j.symm.toLinearMap ∘ₗ i
  replace hi : Injective i' := by simpa [i'] using hi
  let f' := j.symm.toLinearMap ∘ₗ f ∘ₗ (LinearEquiv.ofInjective i' hi).symm.toLinearMap
  replace hf : Surjective f' := by simpa [f'] using hf
  simpa [f'] using injective_of_surjective_of_submodule' f' hf
/-
**OrzechProperty.bijective_of_surjective_of_injective** 是 Mathlib 中的一个定理，位于命名空间 
`OrzechProperty`。
形式化陈述：bijective_of_surjective_of_injective {N : Type w} [AddCommMonoid N] [Modul
e R N] (i f : N ->ₗ[R] M) (hi : Function.Injective i) (hf : Function.Surjective 
f) : Function.Bijective f
参数：i f : N ->ₗ[R] M；hi : Function.Injective i；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrzechProperty.injective_of_surjective_of_injective`：injective_of_surjec
tive_of_injective {N : Type w} [AddCommMonoid N] [Module R N] (i f : N ->ₗ[R] M)
 (hi : Injective i) (hf : Surjective f) :…
-/
theorem bijective_of_surjective_of_injective
    {N : Type w} [AddCommMonoid N] [Module R N]
    (i f : N →ₗ[R] M) (hi : Function.Injective i)
    (hf : Function.Surjective f) : Function.Bijective f :=
  ⟨OrzechProperty.injective_of_surjective_of_injective _ _ hi hf, hf⟩
/-
**OrzechProperty.injective_of_surjective_of_submodule** 是 Mathlib 中的一个定理，位于命名空间 
`OrzechProperty`。
形式化陈述：injective_of_surjective_of_submodule {N : Submodule R M} (f : N ->ₗ[R] M) 
(hf : Surjective f) : Injective f
参数：f : N ->ₗ[R] M；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrzechProperty.injective_of_surjective_of_injective`：injective_of_surjec
tive_of_injective {N : Type w} [AddCommMonoid N] [Module R N] (i f : N ->ₗ[R] M)
 (hi : Injective i) (hf : Surjective f) :…
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
-/
theorem injective_of_surjective_of_submodule
    {N : Submodule R M} (f : N →ₗ[R] M) (hf : Surjective f) : Injective f :=
  injective_of_surjective_of_injective N.subtype f N.injective_subtype hf
/-
**OrzechProperty.injective_of_surjective_endomorphism** 是 Mathlib 中的一个定理，位于命名空间 
`OrzechProperty`。
形式化陈述：injective_of_surjective_endomorphism (f : M ->ₗ[R] M) (hf : Surjective f) 
: Injective f
参数：f : M ->ₗ[R] M；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrzechProperty.injective_of_surjective_of_injective`：injective_of_surjec
tive_of_injective {N : Type w} [AddCommMonoid N] [Module R N] (i f : N ->ₗ[R] M)
 (hi : Injective i) (hf : Surjective f) :…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem injective_of_surjective_endomorphism
    (f : M →ₗ[R] M) (hf : Surjective f) : Injective f :=
  injective_of_surjective_of_injective _ f (LinearEquiv.refl _ _).injective hf
/-
**OrzechProperty.bijective_of_surjective_endomorphism** 是 Mathlib 中的一个定理，位于命名空间 
`OrzechProperty`。
形式化陈述：bijective_of_surjective_endomorphism (f : M ->ₗ[R] M) (hf : Surjective f) 
: Bijective f
参数：f : M ->ₗ[R] M；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrzechProperty.injective_of_surjective_endomorphism`：injective_of_surjec
tive_endomorphism (f : M ->ₗ[R] M) (hf : Surjective f) : Injective f
-/
theorem bijective_of_surjective_endomorphism
    (f : M →ₗ[R] M) (hf : Surjective f) : Bijective f :=
  ⟨injective_of_surjective_endomorphism f hf, hf⟩

end OrzechProperty

