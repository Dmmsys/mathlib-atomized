/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Grassmannians

## Main definitions

- `Module.Grassmannian`: `G(k, M; R)` is the `k`ᵗʰ Grassmannian of the `R`-module `M`. It is defined
  to be the set of submodules of `M` whose **quotient** is locally free of rank `k`. Note that there
  is another convention in literature where the `k`ᵗʰ Grassmannian would instead be `k`-dimensional
  subspaces of a given vector space over a field. See implementation notes below.

- `Module.Grassmannian.functor`: The Grassmannian functor that sends an `R`-algebra `A` to the set
  `G(k, A ⊗[R] M; A)`.

## Implementation notes

In the literature, two conventions exist:

1. The `k`ᵗʰ Grassmannian parametrises `k`-dimensional **subspaces** of a given finite-dimensional
   vector space over a field.
2. The `k`ᵗʰ Grassmannian parametrises **quotients** that are locally free of rank `k`, of a given
   module over a ring.

For the purposes of Algebraic Geometry, the first definition here cannot be generalised to obtain
a scheme to represent the functor, which is why the second definition is the one chosen by
[Grothendieck, EGA I.9.7.3][grothendieck-1971] (Springer edition only), and in EGA V.11
(unpublished).

The first definition in the stated generality (i.e. over a field `F`, and finite-dimensional vector
space `V`) can be recovered from the second definition by noting that `k`-dimensional subspaces of
`V` are canonically equivalent to `(n-k)`-dimensional quotients of `V`, and also to `k`-dimensional
quotients of `V*`, the dual of `V`. In symbols, this means that the first definition is equivalent
to `G(n - k, V; F)` and also to `G(k, V →ₗ[F] F; F)`, where `n` is the dimension of `V`.

## TODO
- Define and recover the subspace-definition (i.e. the first definition above).
- Define `chart x` indexed by `x : Fin k → M` as a subtype consisting of those
  `N ∈ G(k, A ⊗[R] M; A)` such that the composition `R^k → M → M⧸N` is an isomorphism.
- Define `chartFunctor x` to turn `chart x` into a subfunctor of `Module.Grassmannian.functor`. This
  will correspond to an affine open chart in the Grassmannian.
- Grassmannians for schemes and quasi-coherent sheaf of modules.
- Representability of `Module.Grassmannian.functor R M k`.
-/

public section

universe u v w

namespace Module

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (k : ℕ)

/-- `G(k, M; R)` is the `k`ᵗʰ Grassmannian of the `R`-module `M`. It is defined to be the set of
submodules of `M` whose quotient is locally free of rank `k`. Note that there is another convention
in literature where instead the submodule is required to have rank `k`. See the module docstring
of `RingTheory.Grassmannian`. -/
/-
**Module.Grassmannian** 是 Mathlib 中的一个归纳类型，位于命名空间 `Module`。
形式化陈述：(R : Type u) → [inst : CommRing R] → (M : Type v) → [inst_1 : AddCommGroup
 M] → [_root_.Module R M] → ℕ → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G(k, M; R)` is the `k`ᵗʰ Grassmannian of the `R`-module `M`. It is defined to b
e the set of
submodules of `M` whose quotient is locally free of rank `k`. Note that there is
 another convention
in literature where instead the submodule is required to have rank `k`. See the 
module docstring
of `RingTheory.Grassmannian`.
-/
@[stacks 089R] structure Grassmannian extends Submodule R M where
  finite_quotient : Module.Finite R (M ⧸ toSubmodule)
  projective_quotient : Projective R (M ⧸ toSubmodule)
  rankAtStalk_eq : ∀ p, rankAtStalk (R := R) (M ⧸ toSubmodule) p = k

attribute [instance] Grassmannian.finite_quotient Grassmannian.projective_quotient

namespace Grassmannian

@[inherit_doc] scoped notation "G(" k ", " M "; " R ")" => Grassmannian R M k

variable {R M k}

/-
**Module.Grassmannian.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Grassmannian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut G(k, M; R) (Submodule R M) :=
  ⟨toSubmodule⟩
/-
**Module.Grassmannian.ext** 是 Mathlib 中的一个定理，位于命名空间 `Module.Grassmannian`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {M : Type v} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M] {k : ℕ}   {N₁ N₂ : Module.Grassmannian R M k}, N₁.t
oSubmodule = N₂.toSubmodule → N₁ = N₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[ext] lemma ext {N₁ N₂ : G(k, M; R)} (h : (N₁ : Submodule R M) = N₂) : N₁ = N₂ := by
  cases N₁; cases N₂; congr 1

section Functor

open CategoryTheory TensorProduct AlgebraTensorModule

attribute [local ext high] ConcreteCategory.hom_ext

variable {A : Type w} [CommRing A] [Algebra R A]
variable (B : Type w) [CommRing B] [Algebra R B]

section BaseChangeMkQ

variable [Algebra A B] [IsScalarTower R A B] (N : Submodule A (A ⊗[R] M))

/-- The surjective `B`-linear map `B ⊗[R] M → B ⊗[A] ((A ⊗[R] M) ⧸ N)` obtained as the base change
of `N.mkQ` along `A → B` -/
/-
**Module.Grassmannian.baseChangeMkQ** 是 Mathlib 中的一个定义，位于命名空间 `Module.Grassmanni
an`。
形式化陈述：baseChangeMkQ : B otimes[R] M ->ₗ[B] B otimes[A] ((A otimes[R] M) ⧸ N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The surjective `B`-linear map `B ⊗[R] M → B ⊗[A] ((A ⊗[R] M) ⧸ N)` obtained as t
he base change
of `N.mkQ` along `A → B`
-/
def baseChangeMkQ : B ⊗[R] M →ₗ[B] B ⊗[A] ((A ⊗[R] M) ⧸ N) :=
  N.mkQ.baseChange B ∘ₗ (cancelBaseChange R A B B M).symm.toLinearMap

variable {B}
/-
**Module.Grassmannian.baseChangeMkQ_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Module
.Grassmannian`。
形式化陈述：baseChangeMkQ_surjective : Function.Surjective (baseChangeMkQ B N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `LinearMap.baseChange_surjective`：LinearMap.baseChange_surjective (A : Ty
pe*) [Semiring A] [Algebra R A] (hg : Function.Surjective g) : Function.Surjecti
ve (g.baseChange A)
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem baseChangeMkQ_surjective : Function.Surjective (baseChangeMkQ B N) :=
  (LinearMap.baseChange_surjective B (Submodule.mkQ_surjective _)).comp
    (cancelBaseChange R A B B M).symm.surjective

/-- The `B`-linear equivalence `(B ⊗[R] M) ⧸ ker (baseChangeMkQ N) ≃ₗ[B] B ⊗[A] ((A ⊗[R] M) ⧸ N)`
underlying `Module.Grassmannian.map`. -/
/-
**Module.Grassmannian.baseChangeMkQEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Module.Grass
mannian`。
形式化陈述：baseChangeMkQEquiv
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Grassmannian.baseChangeMkQ_surjective`：baseChangeMkQ_surjective :
 Function.Surjective (baseChangeMkQ B N)

--- 原说明 ---
The `B`-linear equivalence `(B ⊗[R] M) ⧸ ker (baseChangeMkQ N) ≃ₗ[B] B ⊗[A] ((A 
⊗[R] M) ⧸ N)`
underlying `Module.Grassmannian.map`.
-/
noncomputable def baseChangeMkQEquiv :=
  (baseChangeMkQ B N).quotKerEquivOfSurjective (baseChangeMkQ_surjective N)

end BaseChangeMkQ

variable {B} (f : A →ₐ[R] B)

/-- The map on Grassmannians induced by base change along an algebra map `A → B`.
Given a submodule `N` of `A ⊗[R] M`, the image is the kernel of the composition
B ⊗[R] M ≃ B ⊗[A] (A ⊗[R] M) → B ⊗[A] ((A ⊗[R] M) ⧸ N)`. -/
/-
**Module.Grassmannian.map** 是 Mathlib 中的一个定义，位于命名空间 `Module.Grassmannian`。
形式化陈述：map (N : G(k, (A otimes[R] M); A)) : G(k, (B otimes[R] M); B)
参数：N : G(k, (A otimes[R] M); A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map on Grassmannians induced by base change along an algebra map `A → B`.
Given a submodule `N` of `A ⊗[R] M`, the image is the kernel of the composition
B ⊗[R] M ≃ B ⊗[A] (A ⊗[R] M) → B ⊗[A] ((A ⊗[R] M) ⧸ N)`.
-/
def map (N : G(k, (A ⊗[R] M); A)) : G(k, (B ⊗[R] M); B) :=
  letI : Algebra A B := f.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' <| IsScalarTower.algebraMap_eq R A B
  haveI equiv := baseChangeMkQEquiv N.toSubmodule
  { toSubmodule := (baseChangeMkQ B N.toSubmodule).ker
    finite_quotient := Module.Finite.equiv equiv.symm
    projective_quotient := Module.Projective.of_equiv equiv.symm
    rankAtStalk_eq p := by
      calc
        _ = rankAtStalk (R := B) (B ⊗[A] ((A ⊗[R] M) ⧸ N.toSubmodule)) p := by
          simpa using congrArg (fun g => g p) <| Module.rankAtStalk_eq_of_equiv equiv
        _ = rankAtStalk (R := A) (A ⊗[R] M ⧸ N.toSubmodule)
            (PrimeSpectrum.comap (algebraMap A B) p) := by
          simpa using Module.rankAtStalk_baseChange ..
        _ = k := N.rankAtStalk_eq _ }
/-
**Module.Grassmannian.map_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Module.Grassman
nian`。
形式化陈述：map_toSubmodule (N : G(k, A otimes[R] M; A)) : letI : Algebra A B
参数：N : G(k, A otimes[R] M; A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem map_toSubmodule (N : G(k, A ⊗[R] M; A)) :
  letI : Algebra A B := f.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' <| IsScalarTower.algebraMap_eq R A B
  (map f N).toSubmodule = (baseChangeMkQ B N.toSubmodule).ker := by rfl

variable (k)
/-
**Module.Grassmannian.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Module.Grassmannian`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {M : Type v} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M] (k : ℕ)   (A : CommAlgCat R) (N : Module.Grassmanni
an (↑A) (TensorProduct R (↑A) M) k),   Module.Grassmannian.map (AlgHom.id R ↑A) 
N = N
参数：k : ℕ；A : CommAlgCat R；N : Module.Grassmannian (↑A) (TensorProduct R (↑A) M) 
k；AlgHom.id R ↑A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Grassmannian.ext`：∀ {R : Type u} [inst : CommRing R] {M : Type v}
 [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {k : ℕ}   {N₁ N₂ : Modul
e.Grassmannia…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `TensorProduct.AlgebraTensorModule.ker_baseChange_comp_cancelBaseChange_s
ymm`：ker_baseChange_comp_cancelBaseChange_symm (f : (A otimes[R] M) ->ₗ[A] N) : 
(f.baseChange A ∘ₗ (cancelBaseChange R A A A M).symm).ker = f.ker
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
-/
@[simp] theorem map_id (A : CommAlgCat R) (N : G(k, A ⊗[R] M; A)) :
    map (.id R A) N = N := by
  ext : 1
  exact (ker_baseChange_comp_cancelBaseChange_symm N.mkQ).trans N.toSubmodule.ker_mkQ

variable {C : Type w} [CommRing C] [Algebra R C]
variable (g : B →ₐ[R] C)
/-
**Module.Grassmannian.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Module.Grassmannian`。
形式化陈述：map_comp (N : G(k, A otimes[R] M; A)) : map (g.comp f) N = map g (map f N)
参数：N : G(k, A otimes[R] M; A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `LinearMap.baseChange_surjective`：LinearMap.baseChange_surjective (A : Ty
pe*) [Semiring A] [Algebra R A] (hg : Function.Surjective g) : Function.Surjecti
ve (g.baseChange A)
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Grassmannian.ext`：∀ {R : Type u} [inst : CommRing R] {M : Type v}
 [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {k : ℕ}   {N₁ N₂ : Modul
e.Grassmannia…
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Module.Grassmannian.map_toSubmodule`：map_toSubmodule (N : G(k, A otimes[
R] M; A)) : letI : Algebra A B
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `_private.Mathlib.RingTheory.Grassmannian.0.Module.Grassmannian.baseChang
eMkQ.eq_1`：∀ {R : Type u} [inst : CommRing R] {M : Type v} [inst_1 : AddCommGrou
p M] [inst_2 : _root_.Module R M] {A : Type w}   [inst_3 : CommRing A] …
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
（共 34 条，此处仅展示前 30 条）
-/
theorem map_comp (N : G(k, A ⊗[R] M; A)) :
    map (g.comp f) N = map g (map f N) := by
  algebraize [f.toRingHom, g.toRingHom, (g.comp f).toRingHom]
  -- FIXME: `algebraize` doesn't generate this instance, even though it seems like it should
  let : IsScalarTower A B C := by apply IsScalarTower.of_algebraMap_eq'; rfl
  let fAB := baseChangeMkQ B N.toSubmodule
  let fAC := baseChangeMkQ C N.toSubmodule
  let fBC := baseChangeMkQ C fAB.ker
  have hfAB : Function.Surjective fAB :=
    (LinearMap.baseChange_surjective B (Submodule.mkQ_surjective _)).comp
      (cancelBaseChange R A B B M).symm.surjective
  let e := (fAB.quotKerEquivOfSurjective hfAB).baseChange B C ≪≫ₗ
    cancelBaseChange A B C C (A ⊗[R] M ⧸ N.toSubmodule)
  ext x
  have hfAC_ker_eq : (map (g.comp f) N).toSubmodule = fAC.ker := map_toSubmodule (g.comp f) N
  have hfBC_ker_eq : (map g (map f N)).toSubmodule = fBC.ker := by
    rw [map_toSubmodule g (map f N), map_toSubmodule f N]
  have hcomp : fAC = e.toLinearMap.comp fBC := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [fAC, fBC, e]
    | tmul c m =>
      simp only [fAC, fBC, e, baseChangeMkQ, LinearMap.comp_apply, cancelBaseChange_symm_tmul,
         LinearMap.baseChange_tmul, Submodule.mkQ_apply, LinearEquiv.coe_trans, LinearEquiv.coe_coe,
         LinearEquiv.coe_baseChange, LinearMap.quotKerEquivOfSurjective_apply_mk]
      simp [fAB, baseChangeMkQ]
    | add x y hx hy =>
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_add] at *
      rw [hx, hy]
  rw [hfAC_ker_eq, hfBC_ker_eq, hcomp, LinearEquiv.ker_comp]

/-- The Grassmannian functor sends an `R`-algebra `A` to `G(k, A ⊗[R] M; A)`. -/
@[expose, simps]
/-
**Module.Grassmannian.functor** 是 Mathlib 中的一个定义，位于命名空间 `Module.Grassmannian`。
形式化陈述：functor : CommAlgCat.{w, u} R ⥤ Type (max v w) where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Grassmannian functor sends an `R`-algebra `A` to `G(k, A ⊗[R] M; A)`.
-/
def functor : CommAlgCat.{w, u} R ⥤ Type (max v w) where
  obj A := G(k, (A ⊗[R] M); A)
  map f := ↾map f.hom
  map_id A := by ext N : 1; exact map_id k A N
  map_comp f g := by ext N : 1; exact map_comp k f.hom g.hom N

end Functor

end Grassmannian

end Module

