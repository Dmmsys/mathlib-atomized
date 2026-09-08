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

/-
**isNoetherian_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_of_surjective {σ : R ->+* S} [RingHomSurjective σ] (f : M ->ₛ
ₗ[σ] P) (hf : LinearMap.range f = ⊤) [IsNoetherian R M] : IsNoetherian S P
参数：f : M ->ₛₗ[σ] P；hf : LinearMap.range f = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_comap_eq_self`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type 
u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddC
ommMonoid M] [ins…
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.FG.map`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type
 u_4} …
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
-/
theorem isNoetherian_of_surjective {σ : R →+* S} [RingHomSurjective σ] (f : M →ₛₗ[σ] P)
    (hf : LinearMap.range f = ⊤) [IsNoetherian R M] :
    IsNoetherian S P :=
  ⟨fun s ↦
    have : (s.comap f).map f = s := Submodule.map_comap_eq_self <| hf.symm ▸ le_top
    this ▸ (IsNoetherian.noetherian _).map _⟩
/-
**isNoetherian_map** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isNoetherian_map {σ : R ->+* S} [RingHomSurjective σ] {s : Submodule R M} 
(f : M ->ₛₗ[σ] P) [IsNoetherian R s] : IsNoetherian S (Submodule.map f s)
参数：f : M ->ₛₗ[σ] P。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_surjective`：isNoetherian_of_surjective {σ : R ->+* S} [R
ingHomSurjective σ] (f : M ->ₛₗ[σ] P) (hf : LinearMap.range f = ⊤) [IsNoetherian
 R M] : IsNoethe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_restrict`：range_restrict (h : forall x in p, f x in q) :
 range (f.restrict h) = comap q.subtype (map f p)
· 使用定理 `Submodule.comap_subtype_self`：comap_subtype_self : comap p.subtype p = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isNoetherian_map {σ : R →+* S} [RingHomSurjective σ] {s : Submodule R M}
    (f : M →ₛₗ[σ] P) [IsNoetherian R s] : IsNoetherian S (Submodule.map f s) :=
  isNoetherian_of_surjective (f.submoduleMap s) (by simp [LinearMap.submoduleMap])
/-
**isNoetherian_range** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isNoetherian_range {σ : R ->+* S} [RingHomSurjective σ] (f : M ->ₛₗ[σ] P) 
[IsNoetherian R M] : IsNoetherian S (LinearMap.range f)
参数：f : M ->ₛₗ[σ] P。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_surjective`：isNoetherian_of_surjective {σ : R ->+* S} [R
ingHomSurjective σ] (f : M ->ₛₗ[σ] P) (hf : LinearMap.range f = ⊤) [IsNoetherian
 R M] : IsNoethe…
· 使用定理 `LinearMap.range_rangeRestrict`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Typ
e u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : Ad
dCommMonoid M] [ins…
-/
instance isNoetherian_range {σ : R →+* S} [RingHomSurjective σ] (f : M →ₛₗ[σ] P)
    [IsNoetherian R M] : IsNoetherian S (LinearMap.range f) :=
  isNoetherian_of_surjective _ f.range_rangeRestrict
/-
**isNoetherian_quotient** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isNoetherian_quotient {A M : Type*} [Ring A] [AddCommGroup M] [SMul R A] [
Module R M] [Module A M] [IsScalarTower R A M] (N : Submodule A M) [IsNoetherian
 R M] : IsNoetherian R (M ⧸ N)
参数：N : Submodule A M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_surjective`：isNoetherian_of_surjective {σ : R ->+* S} [R
ingHomSurjective σ] (f : M ->ₛₗ[σ] P) (hf : LinearMap.range f = ⊤) [IsNoetherian
 R M] : IsNoethe…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
-/
instance isNoetherian_quotient {A M : Type*} [Ring A] [AddCommGroup M] [SMul R A] [Module R M]
    [Module A M] [IsScalarTower R A M] (N : Submodule A M) [IsNoetherian R M] :
    IsNoetherian R (M ⧸ N) :=
  isNoetherian_of_surjective ((Submodule.mkQ N).restrictScalars R) <|
    LinearMap.range_eq_top.mpr N.mkQ_surjective
/-
**isNoetherian_of_linearEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_of_linearEquiv {σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair
 σ σ'] [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) [IsNoetherian R M] : IsNoetherian 
S P
参数：f : M ≃ₛₗ[σ] P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_surjective`：isNoetherian_of_surjective {σ : R ->+* S} [R
ingHomSurjective σ] (f : M ->ₛₗ[σ] P) (hf : LinearMap.range f = ⊤) [IsNoetherian
 R M] : IsNoethe…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
-/
theorem isNoetherian_of_linearEquiv {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ']
    [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) [IsNoetherian R M] : IsNoetherian S P :=
  isNoetherian_of_surjective f.toLinearMap f.range
/-
**LinearEquiv.isNoetherian_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.isNoetherian_iff {σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPai
r σ σ'] [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) : IsNoetherian R M ↔ IsNoetherian
 S P
参数：f : M ≃ₛₗ[σ] P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_linearEquiv`：isNoetherian_of_linearEquiv {σ : R ->+* S} 
{σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) [Is
Noetherian R M] :…
-/
theorem LinearEquiv.isNoetherian_iff {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ']
    [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) : IsNoetherian R M ↔ IsNoetherian S P :=
  ⟨fun _ ↦ isNoetherian_of_linearEquiv f, fun _ ↦ isNoetherian_of_linearEquiv f.symm⟩
/-
**isNoetherian_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_top_iff : IsNoetherian R (⊤ : Submodule R M) ↔ IsNoetherian R
 M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.isNoetherian_iff`：LinearEquiv.isNoetherian_iff {σ : R ->+* S
} {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) :
 IsNoetherian R M …
-/
theorem isNoetherian_top_iff : IsNoetherian R (⊤ : Submodule R M) ↔ IsNoetherian R M :=
  Submodule.topEquiv.isNoetherian_iff
/-
**isNoetherian_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_of_injective [IsNoetherian S P] {σ : R ->+* S} {σ' : S ->+* R
} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ->ₛₗ[σ] P) (hf : Function.I
njective f) : IsNoetherian R M
参数：f : M ->ₛₗ[σ] P；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_linearEquiv`：isNoetherian_of_linearEquiv {σ : R ->+* S} 
{σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) [Is
Noetherian R M] :…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
theorem isNoetherian_of_injective [IsNoetherian S P] {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M →ₛₗ[σ] P) (hf : Function.Injective f) :
    IsNoetherian R M :=
  isNoetherian_of_linearEquiv (LinearEquiv.ofInjective f hf).symm
/-
**fg_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fg_of_injective [IsNoetherian S P] {N : Submodule R M} {σ : R ->+* S} {σ' 
: S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ->ₛₗ[σ] P) (hf : 
Function.Injective f) : N.FG
参数：f : M ->ₛₗ[σ] P；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `isNoetherian_of_injective`：isNoetherian_of_injective [IsNoetherian S P] 
{σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : 
M ->ₛₗ[σ] P) (h…
-/
theorem fg_of_injective [IsNoetherian S P] {N : Submodule R M} {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M →ₛₗ[σ] P)
    (hf : Function.Injective f) : N.FG :=
  haveI := isNoetherian_of_injective f hf
  IsNoetherian.noetherian N

end

namespace Module

variable {R S M N : Type*}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
variable (R M)

-- see Note [lower instance priority]
/-
**Module.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 80) _root_.isNoetherian_of_finite [Finite M] : IsNoetherian R M :=
  ⟨fun s => ⟨(s : Set M).toFinite.toFinset, by rw [Set.Finite.coe_toFinset, Submodule.span_eq]⟩⟩

-- see Note [lower instance priority]
/-
**Module.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsNoetherian.finite [IsNoetherian R M] : Module.Finite R M :=
  ⟨IsNoetherian.noetherian ⊤⟩
/-
**Module.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R₁ S : Type*} [CommSemiring R₁] [Semiring S] [Algebra R₁ S]
    [IsNoetherian R₁ S] (I : Ideal S) : Module.Finite R₁ I :=
  IsNoetherian.finite R₁ ((I : Submodule S S).restrictScalars R₁)

variable {R M}
/-
**Module.Finite.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Module.Finite`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Semi
ring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMono
id N] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module S N]   [IsNoetherian 
S N] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f
 : M →ₛₗ[σ] N),   Function.Injective ⇑f → Module.Finite R M
参数：f : M →ₛₗ[σ] N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fg_of_injective`：fg_of_injective [IsNoetherian S P] {N : Submodule R M} 
{σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : 
M ->ₛ…
-/
theorem Finite.of_injective [IsNoetherian S N] {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M →ₛₗ[σ] N) (hf : Function.Injective f) :
    Module.Finite R M :=
  ⟨fg_of_injective f hf⟩

end Module

section

variable {R S M N P : Type*}
variable [Ring R] [Ring S] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module S P]

open IsNoetherian

/-
**isNoetherian_of_ker_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_of_ker_bot [IsNoetherian S P] {σ : R ->+* S} {σ' : S ->+* R} 
[RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ->ₛₗ[σ] P) (hf : LinearMap.ke
r f = ⊥) : IsNoetherian R M
参数：f : M ->ₛₗ[σ] P；hf : LinearMap.ker f = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_linearEquiv`：isNoetherian_of_linearEquiv {σ : R ->+* S} 
{σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) [Is
Noetherian R M] :…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
-/
theorem isNoetherian_of_ker_bot [IsNoetherian S P] {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M →ₛₗ[σ] P) (hf : LinearMap.ker f = ⊥) :
    IsNoetherian R M :=
  isNoetherian_of_linearEquiv (LinearEquiv.ofInjective f <| LinearMap.ker_eq_bot.mp hf).symm
/-
**fg_of_ker_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fg_of_ker_bot [IsNoetherian S P] {N : Submodule R M} {σ : R ->+* S} {σ' : 
S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ->ₛₗ[σ] P) (hf : Li
nearMap.ker f = ⊥) : N.FG
参数：f : M ->ₛₗ[σ] P；hf : LinearMap.ker f = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `isNoetherian_of_ker_bot`：isNoetherian_of_ker_bot [IsNoetherian S P] {σ :
 R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ->
ₛₗ[σ] P) (hf …
-/
theorem fg_of_ker_bot [IsNoetherian S P] {N : Submodule R M} {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M →ₛₗ[σ] P) (hf : LinearMap.ker f = ⊥) :
    N.FG :=
  haveI := isNoetherian_of_ker_bot f hf
  IsNoetherian.noetherian N

-- False over a semiring: ℕ is a Noetherian ℕ-module but ℕ × ℕ is not.
/-
**isNoetherian_prod** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isNoetherian_prod [IsNoetherian R M] [IsNoetherian R N] : IsNoetherian R (
M × N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.fg_of_fg_map_of_fg_inf_ker`：fg_of_fg_map_of_fg_inf_ker (f : M 
->ₗ[R] P) {s : Submodule R M} (hs1 : (s.map f).FG) (hs2 : (s ⊓ LinearMap.ker f).
FG) : s.FG
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `Submodule.FG.map`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type
 u_4} …
· 使用定理 `Submodule.map_comap_eq_self`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type 
u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddC
ommMonoid M] [ins…
-/
instance isNoetherian_prod [IsNoetherian R M] [IsNoetherian R N] : IsNoetherian R (M × N) :=
  ⟨fun s =>
    Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd R M N) (noetherian _) <|
      have : s ⊓ LinearMap.ker (LinearMap.snd R M N) ≤ LinearMap.range (LinearMap.inl R M N) :=
        fun x ⟨_, hx2⟩ => ⟨x.1, Prod.ext rfl <| Eq.symm <| LinearMap.mem_ker.1 hx2⟩
      Submodule.map_comap_eq_self this ▸ (noetherian _).map _⟩
/-
**isNoetherian_sup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isNoetherian_sup (M₁ M₂ : Submodule R N) [IsNoetherian R M₁] [IsNoetherian
 R M₂] : IsNoetherian R ↥(M₁ ⊔ M₂)
参数：M₁ M₂ : Submodule R N。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `LinearMap.range_coprod`：range_coprod (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃
) : range (f.coprod g) = range f ⊔ range g
-/
instance isNoetherian_sup (M₁ M₂ : Submodule R N) [IsNoetherian R M₁] [IsNoetherian R M₂] :
    IsNoetherian R ↥(M₁ ⊔ M₂) := by
  have := isNoetherian_range (M₁.subtype.coprod M₂.subtype)
  rwa [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype] at this

variable {ι : Type*} [Finite ι]
/-
**isNoetherian_pi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isNoetherian_pi : forall {M : ι -> Type*} [forall i, AddCommGroup (M i)] [
forall i, Module R (M i)] [forall i, IsNoetherian R (M i)], IsNoetherian R (Π i,
 M i)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.induction_empty_option`：Finite.induction_empty_option {P : Type u
 -> Prop} (of_equiv : forall {α β}, α ≃ β -> P α -> P β) (h_empty : P PEmpty) (h
_option : forall {α…
· 使用定理 `isNoetherian_of_linearEquiv`：isNoetherian_of_linearEquiv {σ : R ->+* S} 
{σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) [Is
Noetherian R M] :…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance isNoetherian_pi :
    ∀ {M : ι → Type*} [∀ i, AddCommGroup (M i)]
      [∀ i, Module R (M i)] [∀ i, IsNoetherian R (M i)], IsNoetherian R (Π i, M i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · exact fun e h ↦ isNoetherian_of_linearEquiv (LinearEquiv.piCongrLeft R _ e)
  · infer_instance
  · exact fun ih ↦ isNoetherian_of_linearEquiv (LinearEquiv.piOptionEquivProd R).symm

/-- A version of `isNoetherian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
/-
**isNoetherian_pi'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isNoetherian_pi' [IsNoetherian R M] : IsNoetherian R (ι -> M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `isNoetherian_pi` for non-dependent functions. We need this instanc
e because
sometimes Lean fails to apply the dependent version in non-dependent settings (e
.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`).
-/
instance isNoetherian_pi' [IsNoetherian R M] : IsNoetherian R (ι → M) :=
  isNoetherian_pi
/-
**isNoetherian_iSup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isNoetherian_iSup : forall {M : ι -> Submodule R N} [forall i, IsNoetheria
n R (M i)], IsNoetherian R ↥(⨆ i, M i)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.induction_empty_option`：Finite.induction_empty_option {P : Type u
 -> Prop} (of_equiv : forall {α β}, α ≃ β -> P α -> P β) (h_empty : P PEmpty) (h
_option : forall {α…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.iSup_comp`：Equiv.iSup_comp {g : ι' -> α} (e : ι ≃ ι') : ⨆ x, g (e 
x) = ⨆ y, g y
· 使用定理 `iSup_of_empty`：iSup_of_empty [IsEmpty ι] (f : ι -> α) : iSup f = ⊥
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `iSup_option`：iSup_option (f : Option β -> α) : ⨆ o, f o = f none ⊔ ⨆ b, 
f (Option.some b)
-/
instance isNoetherian_iSup :
    ∀ {M : ι → Submodule R N} [∀ i, IsNoetherian R (M i)], IsNoetherian R ↥(⨆ i, M i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · intro _ _ e h _ _; rw [← e.iSup_comp]; apply h
  · intros; rw [iSup_of_empty]; infer_instance
  · intro _ _ ih _ _; rw [iSup_option]; infer_instance

/-- If the first and final modules in an exact sequence are Noetherian,
  then the middle module is also Noetherian. -/
/-
**isNoetherian_of_range_eq_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_of_range_eq_ker {P : Type*} [AddCommGroup P] [Module R P] [Is
Noetherian R M] [IsNoetherian R P] (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (h : Linear
Map.range f = LinearMap.ker g) : IsNoetherian R N
参数：f : M ->ₗ[R] N；g : N ->ₗ[R] P；h : LinearMap.range f = LinearMap.ker g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_mk`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   WellFoundedGT (Submodule
 R M)…
· 使用定理 `wellFounded_gt_exact_sequence`：wellFounded_gt_exact_sequence {β γ : Type
*} [Preorder β] [Preorder γ] [WellFoundedGT β] [WellFoundedGT γ] (K : α) (f₁ : β
 -> α) (f₂ : α -> β…
· 使用定理 `Submodule.instIsModularLattice`：∀ {R : Type u_10} {M : Type u_11} [inst 
: Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsModularLat
tice (Submodule R M)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Submodule.ker_liftQ_eq_bot`：ker_liftQ_eq_bot (f : M ->ₛₗ[τ₁₂] M₂) (h) (h
' : ker f <= p) : ker (p.liftQ f h) = ⊥
· 使用定理 `LinearMap.surjective_rangeRestrict`：surjective_rangeRestrict : Surjectiv
e f.rangeRestrict
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_comap_eq`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} 
{M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
· 使用定理 `Submodule.range_liftQ`：range_liftQ [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ
₁₂] M₂) (h) : range (p.liftQ f h) = range f
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.comap_map_eq`：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule
 R M) : comap f (map f p) = p ⊔ LinearMap.ker f
· 使用定理 `LinearMap.ker_codRestrict`：ker_codRestrict (p : Submodule R₂ M₂) (f : M 
->ₛₗ[τ₁₂] M₂) (hf) : ker (codRestrict p f hf) = ker f
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f

--- 原说明 ---
If the first and final modules in an exact sequence are Noetherian,
  then the middle module is also Noetherian.
-/
theorem isNoetherian_of_range_eq_ker {P : Type*} [AddCommGroup P] [Module R P] [IsNoetherian R M]
    [IsNoetherian R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : LinearMap.range f = LinearMap.ker g) :
    IsNoetherian R N :=
  isNoetherian_mk <|
    wellFounded_gt_exact_sequence
      (LinearMap.range f)
      (Submodule.map ((LinearMap.ker f).liftQ f le_rfl))
      (Submodule.comap ((LinearMap.ker f).liftQ f le_rfl))
      (Submodule.comap g.rangeRestrict) (Submodule.map g.rangeRestrict)
      (Submodule.gciMapComap <| LinearMap.ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
      (Submodule.giMapComap g.surjective_rangeRestrict)
      (by simp [Submodule.map_comap_eq, inf_comm, Submodule.range_liftQ])
      (by simp [Submodule.comap_map_eq, h])
/-
**isNoetherian_iff_submodule_quotient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_iff_submodule_quotient (S : Submodule R N) : IsNoetherian R N
 ↔ IsNoetherian R S ∧ IsNoetherian R (N ⧸ S)
参数：S : Submodule R N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_range_eq_ker`：isNoetherian_of_range_eq_ker {P : Type*} [
AddCommGroup P] [Module R P] [IsNoetherian R M] [IsNoetherian R P] (f : M ->ₗ[R]
 N) (g : N ->ₗ[R] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
-/
theorem isNoetherian_iff_submodule_quotient (S : Submodule R N) :
    IsNoetherian R N ↔ IsNoetherian R S ∧ IsNoetherian R (N ⧸ S) := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ?_⟩
  apply isNoetherian_of_range_eq_ker S.subtype S.mkQ
  rw [Submodule.ker_mkQ, Submodule.range_subtype]

end

section CommRing

variable (R M N : Type*) [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  [IsNoetherian R M] [Module.Finite R N]

/-
**isNoetherian_linearMap_pi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isNoetherian_linearMap_pi {ι : Type*} [Finite ι] : IsNoetherian R ((ι -> R
) ->ₗ[R] M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_linearEquiv`：isNoetherian_of_linearEquiv {σ : R ->+* S} 
{σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) [Is
Noetherian R M] :…
-/
instance isNoetherian_linearMap_pi {ι : Type*} [Finite ι] : IsNoetherian R ((ι → R) →ₗ[R] M) :=
  let _i : Fintype ι := Fintype.ofFinite ι; isNoetherian_of_linearEquiv (Module.piEquiv ι R M)
/-
**isNoetherian_linearMap** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isNoetherian_linearMap : IsNoetherian R (N ->ₗ[R] M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Finite.exists_fin'`：exists_fin' [Module.Finite R M] : exists (n :
 Nat) (f : (Fin n -> R) ->ₗ[R] M), Surjective f
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `isNoetherian_of_injective`：isNoetherian_of_injective [IsNoetherian S P] 
{σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : 
M ->ₛₗ[σ] P) (h…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Function.Surjective.injective_linearMapComp_right`：∀ {R₁ : Type u_2} {R₂
 : Type u_3} {R₃ : Type u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [
inst : Semiring R₁]   [inst_1 : Semirin…
-/
instance isNoetherian_linearMap : IsNoetherian R (N →ₗ[R] M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
  let g : (N →ₗ[R] M) →ₗ[R] (Fin n → R) →ₗ[R] M := (LinearMap.llcomp R (Fin n → R) N M).flip f
  exact isNoetherian_of_injective g hf.injective_linearMapComp_right

end CommRing

open IsNoetherian Submodule Function

section

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
/-
**IsNoetherian.induction** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNoetherian.induction [IsNoetherian R M] {P : Submodule R M -> Prop} (hgt
 : forall I, (forall J > I, P J) -> P I) (I : Submodule R M) : P I
参数：hgt : forall I, (forall J > I, P J) -> P I；I : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, r y x -> motive y) -> motive x) : motive a

--- 原说明 ---
If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules.
-/
theorem IsNoetherian.induction [IsNoetherian R M] {P : Submodule R M → Prop}
    (hgt : ∀ I, (∀ J > I, P J) → P I) (I : Submodule R M) : P I :=
  IsWellFounded.induction _ I hgt
/-
**LinearMap.isNoetherian_iff_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.isNoetherian_iff_of_bijective {S P} [Semiring S] [AddCommMonoid 
P] [Module S P] {σ : R ->+* S} [RingHomSurjective σ] (l : M ->ₛₗ[σ] P) (hl : Fun
ction.Bijective l) : IsNoetherian R M ↔ IsNoetherian S P
参数：l : M ->ₛₗ[σ] P；hl : Function.Bijective l。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StrictMono.wellFoundedGT`：∀ {α : Type u} {β : Type v} [inst : Preorder α
] [inst_1 : Preorder β] {f : α → β} [WellFoundedGT β],   StrictMono f → WellFoun
dedGT α
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
-/
theorem LinearMap.isNoetherian_iff_of_bijective {S P} [Semiring S] [AddCommMonoid P] [Module S P]
    {σ : R →+* S} [RingHomSurjective σ] (l : M →ₛₗ[σ] P) (hl : Function.Bijective l) :
    IsNoetherian R M ↔ IsNoetherian S P := by
  simp_rw [isNoetherian_iff']
  let e := Submodule.orderIsoMapComapOfBijective l hl
  exact ⟨fun _ ↦ e.symm.strictMono.wellFoundedGT, fun _ ↦ e.strictMono.wellFoundedGT⟩

end

section

variable {R M N P : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [IsNoetherian R M]

/-
**Submodule.finite_ne_bot_of_iSupIndep** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.finite_ne_bot_of_iSupIndep {ι : Type*} {N : ι -> Submodule R M} 
(h : iSupIndep N) : Set.Finite {i | N i != ⊥}
参数：h : iSupIndep N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedGT.finite_ne_bot_of_iSupIndep`：WellFoundedGT.finite_ne_bot_of
_iSupIndep [WellFoundedGT α] {ι : Type*} {t : ι -> α} (ht : iSupIndep t) : Set.F
inite {i | t i != ⊥}
-/
lemma Submodule.finite_ne_bot_of_iSupIndep {ι : Type*} {N : ι → Submodule R M} (h : iSupIndep N) :
    Set.Finite {i | N i ≠ ⊥} :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep h

/-- A linearly-independent family of vectors in a module over a non-trivial ring must be finite if
the module is Noetherian. -/
/-
**LinearIndependent.finite_of_isNoetherian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.finite_of_isNoetherian [Nontrivial R] {ι} {v : ι -> M} (
hv : LinearIndependent R v) : Finite ι
参数：hv : LinearIndependent R v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedGT.finite_of_iSupIndep`：WellFoundedGT.finite_of_iSupIndep [We
llFoundedGT α] {ι : Type*} {t : ι -> α} (ht : iSupIndep t) (h_ne_bot : forall i,
 t i != ⊥) : Finite ι
· 使用定理 `LinearIndependent.iSupIndep_span_singleton`：LinearIndependent.iSupIndep_
span_singleton (hv : LinearIndependent R v) : iSupIndep fun i => R ∙ v i
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A linearly-independent family of vectors in a module over a non-trivial ring mus
t be finite if
the module is Noetherian.
-/
theorem LinearIndependent.finite_of_isNoetherian [Nontrivial R] {ι} {v : ι → M}
    (hv : LinearIndependent R v) : Finite ι :=
  WellFoundedGT.finite_of_iSupIndep hv.iSupIndep_span_singleton fun i _ ↦ hv.ne_zero i (by simp_all)

variable [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P] [Nontrivial P]

/-- If `P × N` embeds into `N` for some nontrivial module `P`, then `N` cannot be a Noetherian
module. Lemma 1.36 of Chapter 1 in [lam_1999]. -/
/-
**IsNoetherian.subsingleton_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNoetherian.subsingleton_of_injective {P : Type*} [AddCommMonoid P] [Modu
le R P] {f : P × M ->ₗ[R] M} (inj : Injective f) : Subsingleton P
参数：inj : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_forall_eq`：∀ {α : Sort u_1} (x : α), (∀ (y : α), y = x) 
→ Subsingleton α
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LinearMap.exists_finsupp_nat_of_prod_injective`：exists_finsupp_nat_of_pr
od_injective (inj : Injective f) : exists g : (Nat ->₀ P) ->ₗ[R] M, Injective g
· 使用定理 `Infinite.not_finite`：∀ {α : Sort u_3} [self : Infinite α], ¬Finite α
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `WellFoundedGT.finite_of_iSupIndep`：WellFoundedGT.finite_of_iSupIndep [We
llFoundedGT α] {ι : Type*} {t : ι -> α} (ht : iSupIndep t) (h_ne_bot : forall i,
 t i != ⊥) : Finite ι
· 使用定理 `LinearMap.iSupIndep_map`：LinearMap.iSupIndep_map (f : M ->ₗ[R] M') (inj 
: Injective f) {m : ι -> Submodule R M} (ind : iSupIndep m) : iSupIndep fun i =>
 (m i).map f
· 使用定理 `iSupIndep_range_lsingle`：iSupIndep_range_lsingle : iSupIndep fun i : ι =
> LinearMap.range (Finsupp.lsingle (R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
If `P × N` embeds into `N` for some nontrivial module `P`, then `N` cannot be a 
Noetherian
module. Lemma 1.36 of Chapter 1 in [lam_1999].
-/
theorem IsNoetherian.subsingleton_of_injective {P : Type*} [AddCommMonoid P] [Module R P]
    {f : P × M →ₗ[R] M} (inj : Injective f) : Subsingleton P :=
  subsingleton_of_forall_eq 0 fun p ↦ by_contra fun _ ↦
    have ⟨g, inj⟩ := LinearMap.exists_finsupp_nat_of_prod_injective inj
    Infinite.not_finite <| WellFoundedGT.finite_of_iSupIndep
      (g.iSupIndep_map inj (iSupIndep_range_lsingle ℕ R P))
      fun i ↦ (Submodule.ne_bot_iff _).mpr ⟨_, ⟨_, ⟨p, rfl⟩, rfl⟩, by simpa [inj]⟩
/-
**LinearIndependent.set_finite_of_isNoetherian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.set_finite_of_isNoetherian [Nontrivial R] {s : Set M} (h
i : LinearIndependent R ((↑) : s -> M)) : s.Finite
参数：hi : LinearIndependent R ((↑) : s -> M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.finite_of_isNoetherian`：LinearIndependent.finite_of_is
Noetherian [Nontrivial R] {ι} {v : ι -> M} (hv : LinearIndependent R v) : Finite
 ι
-/
theorem LinearIndependent.set_finite_of_isNoetherian [Nontrivial R] {s : Set M}
    (hi : LinearIndependent R ((↑) : s → M)) : s.Finite :=
  hi.finite_of_isNoetherian

/-- A sequence `f` of submodules of a Noetherian module,
with `f (n+1)` disjoint from the supremum of `f 0`, ..., `f n`,
is eventually zero. -/
/-
**IsNoetherian.disjoint_partialSups_eventually_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNoetherian.disjoint_partialSups_eventually_bot (f : Nat -> Submodule R M
) (h : forall n, Disjoint (partialSups f n) (f (n + 1))) : exists n : Nat, foral
l m, n <= m -> f m = ⊥
参数：f : Nat -> Submodule R M；h : forall n, Disjoint (partialSups f n) (f (n + 1))
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotone_stabilizes_iff_noetherian`：monotone_stabilizes_iff_noetherian :
 (forall f : Nat ->o Submodule R M, exists n, forall m, n <= m -> f n = f m) ↔ I
sNoetherian R M
· 使用定理 `Disjoint.eq_bot_of_ge`：Disjoint.eq_bot_of_ge (hab : Disjoint a b) : b <=
 a -> b = ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `partialSups_add_one`：partialSups_add_one [Add ι] [One ι] [LocallyFiniteO
rderBot ι] [SuccAddOrder ι] (f : ι -> α) (i : ι) : partialSups f (i + 1) = parti
alSups f …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canon
icallyOrderedAdd α] {a b c : α}, a ≤ b → a ≤ b + c
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Nat.succ_le_succ_iff`：∀ {a b : ℕ}, a.succ ≤ b.succ ↔ a ≤ b

--- 原说明 ---
A sequence `f` of submodules of a Noetherian module,
with `f (n+1)` disjoint from the supremum of `f 0`, ..., `f n`,
is eventually zero.
-/
theorem IsNoetherian.disjoint_partialSups_eventually_bot
    (f : ℕ → Submodule R M) (h : ∀ n, Disjoint (partialSups f n) (f (n + 1))) :
    ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊥ := by
  -- A little off-by-one cleanup first:
  suffices t : ∃ n : ℕ, ∀ m, n ≤ m → f (m + 1) = ⊥ by
    obtain ⟨n, w⟩ := t
    use n + 1
    rintro (_ | m) p
    · cases p
    · apply w
      exact Nat.succ_le_succ_iff.mp p
  obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance (partialSups f)
  refine ⟨n, fun m p ↦ (h m).eq_bot_of_ge <| sup_eq_left.mp ?_⟩
  simpa only [partialSups_add_one] using (w (m + 1) <| le_add_right p).symm.trans <| w m p

end

-- see Note [lower instance priority]
/-- Modules over the trivial ring are Noetherian. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Modules over the trivial ring are Noetherian.
-/
instance (priority := 100) isNoetherian_of_subsingleton (R M) [Subsingleton R] [Semiring R]
    [AddCommMonoid M] [Module R M] : IsNoetherian R M :=
  haveI := Module.subsingleton R M
  isNoetherian_of_finite R M
/-
**isNoetherian_of_submodule_of_noetherian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_of_submodule_of_noetherian (R M) [Semiring R] [AddCommMonoid 
M] [Module R M] (N : Submodule R M) (h : IsNoetherian R M) : IsNoetherian R N
参数：R M；N : Submodule R M；h : IsNoetherian R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_mk`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   WellFoundedGT (Submodule
 R M)…
· 使用定理 `OrderEmbedding.wellFounded`：∀ {α : Type u_2} {β : Type u_3} [inst : Preo
rder α] [inst_1 : Preorder β] (f : α ↪o β),   (WellFounded fun x1 x2 => x1 < x2)
 → WellFounded f…
· 使用定理 `IsNoetherian.wf`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   IsNoetherian R M → WellF
ounde…
-/
theorem isNoetherian_of_submodule_of_noetherian (R M) [Semiring R] [AddCommMonoid M] [Module R M]
    (N : Submodule R M) (h : IsNoetherian R M) : IsNoetherian R N :=
  isNoetherian_mk ⟨OrderEmbedding.wellFounded (Submodule.MapSubtype.orderEmbedding N).dual h.wf⟩

/-- If `M / S / R` is a scalar tower, and `M / R` is Noetherian, then `M / S` is
also Noetherian. -/
/-
**isNoetherian_of_tower** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_of_tower (R) {S M} [Semiring R] [Semiring S] [AddCommMonoid M
] [SMul R S] [Module S M] [Module R M] [IsScalarTower R S M] (h : IsNoetherian R
 M) : IsNoetherian S M
参数：R；h : IsNoetherian R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_mk`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   WellFoundedGT (Submodule
 R M)…
· 使用定理 `OrderEmbedding.wellFounded`：∀ {α : Type u_2} {β : Type u_3} [inst : Preo
rder α] [inst_1 : Preorder β] (f : α ↪o β),   (WellFounded fun x1 x2 => x1 < x2)
 → WellFounded f…
· 使用定理 `IsNoetherian.wf`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   IsNoetherian R M → WellF
ounde…

--- 原说明 ---
If `M / S / R` is a scalar tower, and `M / R` is Noetherian, then `M / S` is
also Noetherian.
-/
theorem isNoetherian_of_tower (R) {S M} [Semiring R] [Semiring S] [AddCommMonoid M] [SMul R S]
    [Module S M] [Module R M] [IsScalarTower R S M] (h : IsNoetherian R M) : IsNoetherian S M :=
  isNoetherian_mk ⟨(Submodule.restrictScalarsEmbedding R S M).dual.wellFounded h.wf⟩
/-
**isNoetherian_of_isNoetherianRing_of_finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isNoetherian_of_isNoetherianRing_of_finite (R M : Type*) [Ring R] [AddComm
Group M] [Module R M] [IsNoetherianRing R] [Module.Finite R M] : IsNoetherian R 
M
参数：R M : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Finite.exists_fin'`：exists_fin' [Module.Finite R M] : exists (n :
 Nat) (f : (Fin n -> R) ->ₗ[R] M), Surjective f
· 使用定理 `isNoetherian_of_surjective`：isNoetherian_of_surjective {σ : R ->+* S} [R
ingHomSurjective σ] (f : M ->ₛₗ[σ] P) (hf : LinearMap.range f = ⊤) [IsNoetherian
 R M] : IsNoethe…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance isNoetherian_of_isNoetherianRing_of_finite (R M : Type*)
    [Ring R] [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M] :
    IsNoetherian R M :=
  have ⟨_, _, h⟩ := Module.Finite.exists_fin' R M
  isNoetherian_of_surjective _ (LinearMap.range_eq_top.mpr h)
/-
**isNoetherian_of_fg_of_noetherian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_of_fg_of_noetherian {R M} [Ring R] [AddCommGroup M] [Module R
 M] (N : Submodule R M) [I : IsNoetherianRing R] (hN : N.FG) : IsNoetherian R N
参数：N : Submodule R M；hN : N.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
-/
theorem isNoetherian_of_fg_of_noetherian {R M} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [I : IsNoetherianRing R] (hN : N.FG) : IsNoetherian R N :=
  haveI : Module.Finite R N := .of_fg hN; inferInstance

/-- In a module over a Noetherian ring, the submodule generated by finitely many vectors is
Noetherian. -/
/-
**isNoetherian_span_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_span_of_finite (R) {M} [Ring R] [AddCommGroup M] [Module R M]
 [IsNoetherianRing R] {A : Set M} (hA : A.Finite) : IsNoetherian R (Submodule.sp
an R A)
参数：R；hA : A.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_fg_of_noetherian`：isNoetherian_of_fg_of_noetherian {R M}
 [Ring R] [AddCommGroup M] [Module R M] (N : Submodule R M) [I : IsNoetherianRin
g R] (hN : N.FG) : IsN…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.fg_def`：fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, 
S.Finite ∧ span R S = N

--- 原说明 ---
In a module over a Noetherian ring, the submodule generated by finitely many vec
tors is
Noetherian.
-/
theorem isNoetherian_span_of_finite (R) {M} [Ring R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] {A : Set M} (hA : A.Finite) : IsNoetherian R (Submodule.span R A) :=
  isNoetherian_of_fg_of_noetherian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)
/-
**IsNoetherianRing.of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNoetherianRing.of_finite (R S) [Ring R] [Ring S] [Module R S] [IsScalarT
ower R S S] [IsNoetherianRing R] [Module.Finite R S] : IsNoetherianRing S
参数：R S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_tower`：isNoetherian_of_tower (R) {S M} [Semiring R] [Sem
iring S] [AddCommMonoid M] [SMul R S] [Module S M] [Module R M] [IsScalarTower R
 S M] (h : …
-/
theorem IsNoetherianRing.of_finite (R S) [Ring R] [Ring S] [Module R S] [IsScalarTower R S S]
    [IsNoetherianRing R] [Module.Finite R S] : IsNoetherianRing S :=
  isNoetherian_of_tower R inferInstance
/-
**isNoetherianRing_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherianRing_of_surjective (R) [Semiring R] (S) [Semiring S] (f : R ->
+* S) (hf : Function.Surjective f) [H : IsNoetherianRing R] : IsNoetherianRing S
参数：R；S；f : R ->+* S；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_mk`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   WellFoundedGT (Submodule
 R M)…
· 使用定理 `OrderEmbedding.wellFounded`：∀ {α : Type u_2} {β : Type u_3} [inst : Preo
rder α] [inst_1 : Preorder β] (f : α ↪o β),   (WellFounded fun x1 x2 => x1 < x2)
 → WellFounded f…
· 使用定理 `IsNoetherian.wf`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   IsNoetherian R M → WellF
ounde…
-/
theorem isNoetherianRing_of_surjective (R) [Semiring R] (S) [Semiring S] (f : R →+* S)
    (hf : Function.Surjective f) [H : IsNoetherianRing R] : IsNoetherianRing S :=
  isNoetherian_mk ⟨OrderEmbedding.wellFounded (Ideal.orderEmbeddingOfSurjective f hf).dual H.wf⟩
/-
**isNoetherianRing_rangeS** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isNoetherianRing_rangeS {R} [Semiring R] {S} [Semiring S] (f : R ->+* S) [
IsNoetherianRing R] : IsNoetherianRing f.rangeS
参数：f : R ->+* S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherianRing_of_surjective`：isNoetherianRing_of_surjective (R) [Semi
ring R] (S) [Semiring S] (f : R ->+* S) (hf : Function.Surjective f) [H : IsNoet
herianRing R] : IsNo…
· 使用定理 `RingHom.rangeSRestrict_surjective`：rangeSRestrict_surjective (f : R ->+*
 S) : Function.Surjective f.rangeSRestrict
-/
instance isNoetherianRing_rangeS {R} [Semiring R] {S} [Semiring S] (f : R →+* S)
    [IsNoetherianRing R] : IsNoetherianRing f.rangeS :=
  isNoetherianRing_of_surjective R f.rangeS f.rangeSRestrict f.rangeSRestrict_surjective
/-
**isNoetherianRing_range** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isNoetherianRing_range {R} [Ring R] {S} [Ring S] (f : R ->+* S) [IsNoether
ianRing R] : IsNoetherianRing f.range
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isNoetherianRing_range {R} [Ring R] {S} [Ring S] (f : R →+* S)
    [IsNoetherianRing R] : IsNoetherianRing f.range :=
  isNoetherianRing_rangeS f
/-
**isNoetherianRing_of_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherianRing_of_ringEquiv (R) [Semiring R] {S} [Semiring S] (f : R ≃+*
 S) [IsNoetherianRing R] : IsNoetherianRing S
参数：R；f : R ≃+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherianRing_of_surjective`：isNoetherianRing_of_surjective (R) [Semi
ring R] (S) [Semiring S] (f : R ->+* S) (hf : Function.Surjective f) [H : IsNoet
herianRing R] : IsNo…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem isNoetherianRing_of_ringEquiv (R) [Semiring R] {S} [Semiring S] (f : R ≃+* S)
    [IsNoetherianRing R] : IsNoetherianRing S :=
  isNoetherianRing_of_surjective R S f.toRingHom f.toEquiv.surjective
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S} [Semiring R] [Semiring S] [IsNoetherianRing R] [IsNoetherianRing S] :
    IsNoetherianRing (R × S) := by
  rw [IsNoetherianRing, isNoetherian_iff'] at *
  exact Ideal.idealProdEquiv.toOrderEmbedding.wellFoundedGT
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι} [Finite ι] : ∀ {R : ι → Type*} [Π i, Semiring (R i)] [∀ i, IsNoetherianRing (R i)],
    IsNoetherianRing (Π i, R i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · exact fun e h ↦ isNoetherianRing_of_ringEquiv _ (.piCongrLeft _ e)
  · infer_instance
  · exact fun ih ↦ isNoetherianRing_of_ringEquiv _ (.symm .piOptionEquivProd)

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- A submodule contained in an noetherian submodule is FG. -/
/-
**Submodule.FG.of_le_of_isNoetherian** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {S T : Submodule R M} [IsNoetherian R ↥T], S ≤ T 
→ S.FG
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isNoetherian_submodule`：isNoetherian_submodule {N : Submodule R M} : IsN
oetherian R N ↔ forall s : Submodule R M, s <= N -> s.FG

--- 原说明 ---
A submodule contained in an noetherian submodule is FG.
-/
theorem FG.of_le_of_isNoetherian {S T : Submodule R M} [IsNoetherian R T] (hST : S ≤ T) : S.FG :=
  isNoetherian_submodule.mp inferInstance _ hST

/-- A submodule contained in an FG submodule is FG over noetherian rings. -/
/-
**Submodule.FG.of_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   [IsNoetherianRing R] {S T : Submodule R M}, T.FG 
→ S ≤ T → S.FG
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.FG.of_le_of_isNoetherian`：∀ {R : Type u_1} {M : Type u_2} [ins
t : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {S T : Subm
odule R M} [IsNoetherian…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG

--- 原说明 ---
A submodule contained in an FG submodule is FG over noetherian rings.
-/
lemma FG.of_le [IsNoetherianRing R] {S T : Submodule R M} (hT : T.FG) (hST : S ≤ T) : S.FG := by
  rw [← Module.Finite.iff_fg] at hT
  exact FG.of_le_of_isNoetherian hST

/-- If `S` is disjoint from `T` and `M ⧸ T` is a noetherian module, then `S` is FG.
See also `Submodule.CoFG.fg_of_disjoint`. -/
/-
**Submodule.FG.of_disjoint_of_isNoetherian_quotient** 是 Mathlib 中的一个定理，位于命名空间 `S
ubmodule.FG`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {S T : Submodule R M} [IsNoetherian R (M ⧸ T)], D
isjoint S T → S.FG
参数：M ⧸ T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `Module.Finite.of_injective`：∀ {R : Type u_1} {S : Type u_2} {M : Type u_
3} {N : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommM
onoid M] [inst_3…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
If `S` is disjoint from `T` and `M ⧸ T` is a noetherian module, then `S` is FG.
See also `Submodule.CoFG.fg_of_disjoint`.
-/
theorem FG.of_disjoint_of_isNoetherian_quotient {S T : Submodule R M} [IsNoetherian R (M ⧸ T)]
    (hST : Disjoint S T) : S.FG :=
  Module.Finite.iff_fg.mp <| .of_injective (T.mkQ.domRestrict S) (by simp [hST])

end Submodule

universe w v u

variable (R : Type u) [CommRing R]

/-
**Module.exists_finite_presentation** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.exists_finite_presentation [Small.{v} R] (M : Type v) [AddCommGroup
 M] [Module R M] [Module.Finite R M] : exists (P : Type v) (_ : AddCommGroup P) 
(_ : Module R P) (_ : Module.Free R P) (_ : Module.Finite R P) (f : P ->ₗ[R] M),
 Function.Surjective f
参数：M : Type v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Finite.exists_fin'`：exists_fin' [Module.Finite R M] : exists (n :
 Nat) (f : (Fin n -> R) ->ₗ[R] M), Surjective f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Free.finsupp`：∀ (R : Type u_1) (M : Type u_2) (ι : Type u_3) [ins
t : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Modul
e.Free R …
-/
theorem Module.exists_finite_presentation [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : ∃ (P : Type v) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Free R P)
      (_ : Module.Finite R P) (f : P →ₗ[R] M), Function.Surjective f := by
  rcases Module.Finite.exists_fin' R M with ⟨m, f', hf'⟩
  let f := f'.comp ((Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)).trans
      (Finsupp.linearEquivFunOnFinite R R (Fin m))).1
  use (Fin m →₀ Shrink.{v, u} R), inferInstance, inferInstance, inferInstance, inferInstance, f
  simpa [f] using hf'
