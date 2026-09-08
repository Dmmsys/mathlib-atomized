/-
Copyright (c) 2025 Antoine Chambert-Loir & María-Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir & María-Inés de Frutos-Fernández
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG

/-! # Polynomial laws on modules

Let `M` and `N` be a modules over a commutative ring `R`.
A polynomial law `f : PolynomialLaw R M N`, with notation `f : M →ₚₗₗ[R] N`,
is a “law” that assigns a natural map `PolynomialLaw.toFun' f S : S ⊗[R] M → S ⊗[R] N`
for every `R`-algebra `S`.

For type-theoretic reasons, if `R : Type u`, then the definition of the polynomial map `f`
is restricted to `R`-algebras `S` such that `S : Type u`.
Using the fact that a module is the direct limit of its finitely generated submodules, that a
finitely generated subalgebra is a quotient of a polynomial ring in the universe `u`, plus
the commutation of tensor products with direct limits, we extend the functor
to all `R`-algebras.

The two fields involving the definition of `PolynomialLaw`,
`PolynomialLaw.toFun'` and `PolynomialLaw.isCompat'` are primed.
They are superseded by their universe-polymorphic counterparts,
the definition `PolynomialLaw.toFun` and the lemma `PolynomialLaw.isCompat`
which should be used once the theory is properly stated.

For constructions of general definitions of `PolynomialLaw`
at a universe-polymorphic level, one needs to lift
elements in a tensor product to smaller universes.
For this, one can make use of
`PolynomialLaw.exists_lift` or `PolynomialLaw.exists_lift'`,
or establish appropriate generalizations.

## Main definitions/lemmas

* Instance : `Module R (M →ₚₗ[R] N)` shows that polynomial laws form an `R`-module.

* `PolynomialLaw.ground f` is the map `M → N` corresponding to `PolynomialLaw.toFun' f R` under
  the isomorphisms `R ⊗[R] M ≃ₗ[R] M`, and similarly for `N`.

In further works, we construct the coefficients of a polynomial law and show the relation with
polynomials (when the module `M` is free and finite).

## Implementation notes

In the literature, the theory is written for commutative rings, but this implementation
only assumes `R` is a commutative semiring.

## References

* [Roby, Norbert. 1963. «Lois polynomes et lois formelles en théorie des modules».
  Annales scientifiques de l’École Normale Supérieure 80 (3): 213‑348](Roby-1963)

-/

@[expose] public section

universe u v w

noncomputable section PolynomialLaw

open scoped TensorProduct

open LinearMap TensorProduct AlgHom RingCon

/-- A polynomial law `M →ₚₗ[R] N` between `R`-modules is a functorial family of maps
`S ⊗[R] M → S ⊗[R] N`, for all `R`-algebras `S`.

For universe reasons, `S` has to be restricted to the same universe as `R`. -/
@[ext]
/-
**PolynomialLaw** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：PolynomialLaw (R : Type u) [CommSemiring R] (M : Type*) [AddCommMonoid M] 
[Module R M] (N : Type*) [AddCommMonoid N] [Module R N] where /-- The functions 
`S ⊗[R] M → S ⊗[R] N` underlying a polynomial law -/ toFun' (S : Type u) [CommSe
miring S] [Algebra R S] : S otimes[R] M -> S otimes[R] N /-- The compatibility r
elations between the functions underlying a polynomial law -/ isCompat' {S : Typ
e u} [CommSemiring S] [Algebra R S] {S' : Type u} [CommSemiring S'] [Algebra R S
'] (φ : S ->ₐ[R] S') : φ.t
参数：R : Type u；M : Type*；N : Type*；S : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A polynomial law `M →ₚₗ[R] N` between `R`-modules is a functorial family of maps
`S ⊗[R] M → S ⊗[R] N`, for all `R`-algebras `S`.

For universe reasons, `S` has to be restricted to the same universe as `R`.
-/
structure PolynomialLaw (R : Type u) [CommSemiring R]
    (M : Type*) [AddCommMonoid M] [Module R M] (N : Type*) [AddCommMonoid N] [Module R N] where
  /-- The functions `S ⊗[R] M → S ⊗[R] N` underlying a polynomial law -/
  toFun' (S : Type u) [CommSemiring S] [Algebra R S] : S ⊗[R] M → S ⊗[R] N
  /-- The compatibility relations between the functions underlying a polynomial law -/
  isCompat' {S : Type u} [CommSemiring S] [Algebra R S]
    {S' : Type u} [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S') :
    φ.toLinearMap.rTensor N ∘ toFun' S = toFun' S' ∘ φ.toLinearMap.rTensor M := by aesop

/-- `M →ₚₗ[R] N` is the type of `R`-polynomial laws from `M` to `N`. -/
notation:25 M " →ₚₗ[" R:25 "] " N:0 => PolynomialLaw R M N

@[local simp]
/-
**PolynomialLaw.isCompat_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PolynomialLaw.isCompat_apply' {R : Type u} [CommSemiring R] {M : Type*} [A
ddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N] {f : M -
>ₚₗ[R] N} {S : Type u} [CommSemiring S] [Algebra R S] {S' : Type u} [CommSemirin
g S'] [Algebra R S'] (φ : S ->ₐ[R] S') (x : S otimes[R] M) : (φ.toLinearMap.rTen
sor N) ((f.toFun' S) x) = (f.toFun' S') (φ.toLinearMap.rTensor M x)
参数：φ : S ->ₐ[R] S'；x : S otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
· 使用定理 `PolynomialLaw.isCompat'`：∀ {R : Type u} [inst : CommSemiring R] {M : Typ
e u_1} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Type u_2} 
[inst_3 : Add…
-/
theorem PolynomialLaw.isCompat_apply'
    {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
    {N : Type*} [AddCommMonoid N] [Module R N] {f : M →ₚₗ[R] N}
    {S : Type u} [CommSemiring S] [Algebra R S] {S' : Type u} [CommSemiring S'] [Algebra R S']
    (φ : S →ₐ[R] S') (x : S ⊗[R] M) :
    (φ.toLinearMap.rTensor N) ((f.toFun' S) x) = (f.toFun' S') (φ.toLinearMap.rTensor M x) := by
  simpa only using! congr_fun (f.isCompat' φ) x

attribute [local simp] PolynomialLaw.isCompat_apply'

namespace PolynomialLaw

section Module

section CommSemiring

variable {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N] (r a b : R) (f g : M →ₚₗ[R] N)

/-
**PolynomialLaw.** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (M →ₚₗ[R] N) := ⟨{ toFun' _ := 0 }⟩

@[simp]
/-
**PolynomialLaw.zero_def** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：zero_def (S : Type u) [CommSemiring S] [Algebra R S] : (0 : PolynomialLaw 
R M N).toFun' S = 0
参数：S : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
-/
theorem zero_def (S : Type u) [CommSemiring S] [Algebra R S] :
    (0 : PolynomialLaw R M N).toFun' S = 0 := rfl
/-
**PolynomialLaw.** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (PolynomialLaw R M N) := ⟨Zero.zero⟩

/-- The identity as a polynomial law -/
/-
**PolynomialLaw.id** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialLaw`。
形式化陈述：id : M ->ₚₗ[R] M where toFun' S _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity as a polynomial law
-/
def id : M →ₚₗ[R] M where
  toFun' S _ _ := _root_.id
/-
**PolynomialLaw.id_apply'** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：id_apply' {S : Type u} [CommSemiring S] [Algebra R S] : (id : M ->ₚₗ[R] M)
.toFun' S = _root_.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
-/
theorem id_apply' {S : Type u} [CommSemiring S] [Algebra R S] :
    (id : M →ₚₗ[R] M).toFun' S = _root_.id := rfl

/-- The sum of two polynomial laws -/
/-
**PolynomialLaw.add** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialLaw`。
形式化陈述：add : M ->ₚₗ[R] N where toFun' S _ _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…

--- 原说明 ---
The sum of two polynomial laws
-/
noncomputable def add : M →ₚₗ[R] N where
  toFun' S _ _ := f.toFun' S + g.toFun' S
/-
**PolynomialLaw.** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (PolynomialLaw R M N) := ⟨add⟩

@[simp]
/-
**PolynomialLaw.add_def** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：add_def (S : Type u) [CommSemiring S] [Algebra R S] : (f + g).toFun' S = f
.toFun' S + g.toFun' S
参数：S : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
-/
theorem add_def (S : Type u) [CommSemiring S] [Algebra R S] :
    (f + g).toFun' S = f.toFun' S + g.toFun' S := rfl
/-
**PolynomialLaw.add_def_apply** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：add_def_apply (S : Type u) [CommSemiring S] [Algebra R S] (m : S otimes[R]
 M) : (f + g).toFun' S m = f.toFun' S m + g.toFun' S m
参数：S : Type u；m : S otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
-/
theorem add_def_apply (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    (f + g).toFun' S m = f.toFun' S m + g.toFun' S m := rfl

/-- External multiplication of a `f : M →ₚₗ[R] N` by `r : R` -/
/-
**PolynomialLaw.smul** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialLaw`。
形式化陈述：smul : M ->ₚₗ[R] N where toFun' S _ _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…

--- 原说明 ---
External multiplication of a `f : M →ₚₗ[R] N` by `r : R`
-/
def smul : M →ₚₗ[R] N where
  toFun' S _ _ := r • f.toFun' S
/-
**PolynomialLaw.** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul R (M →ₚₗ[R] N) := ⟨smul⟩

@[simp]
/-
**PolynomialLaw.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：smul_def (S : Type u) [CommSemiring S] [Algebra R S] : (r • f).toFun' S = 
r • f.toFun' S
参数：S : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
-/
theorem smul_def (S : Type u) [CommSemiring S] [Algebra R S] :
    (r • f).toFun' S = r • f.toFun' S := rfl
/-
**PolynomialLaw.smul_def_apply** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：smul_def_apply (S : Type u) [CommSemiring S] [Algebra R S] (m : S otimes[R
] M) : (r • f).toFun' S m = r • f.toFun' S m
参数：S : Type u；m : S otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
-/
theorem smul_def_apply (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    (r • f).toFun' S m = r • f.toFun' S m := rfl
/-
**PolynomialLaw.add_smul** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：add_smul : (a + b) • f = a • f + b • f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.ext`：∀ {R : Type u} {inst : CommSemiring R} {M : Type u_1}
 {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   {N : Type u_2} {inst_
3 : Add…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_smul : (a + b) • f = a • f + b • f := by
  ext; simp only [add_def, smul_def, _root_.add_smul]
/-
**PolynomialLaw.zero_smul** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：zero_smul : (0 : R) • f = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.ext`：∀ {R : Type u} {inst : CommSemiring R} {M : Type u_1}
 {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   {N : Type u_2} {inst_
3 : Add…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_smul : (0 : R) • f = 0 := by
  ext S; simp only [smul_def, _root_.zero_smul, zero_def, Pi.zero_apply]
/-
**PolynomialLaw.one_smul** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：one_smul : (1 : R) • f = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.ext`：∀ {R : Type u} {inst : CommSemiring R} {M : Type u_1}
 {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   {N : Type u_2} {inst_
3 : Add…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_smul : (1 : R) • f = f := by
  ext S; simp only [smul_def, Pi.smul_apply, _root_.one_smul]
/-
**PolynomialLaw.** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction R (M →ₚₗ[R] N) where
  one_smul := one_smul
  mul_smul a b f := by ext; simp only [smul_def, mul_smul]
/-
**PolynomialLaw.** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid (M →ₚₗ[R] N) where
  add_assoc f g h := by ext; simp only [add_def, add_assoc]
  zero_add f := by ext; simp only [add_def, zero_add, zero_def]
  add_zero f := by ext; simp only [add_def, add_zero, zero_def]
  nsmul n f := (n : R) • f
  nsmul_zero f := by simp_rw [HSMul.hSMul, SMul.smul]; simp only [Nat.cast_zero, zero_smul f]
  nsmul_succ n f := by
    simp_rw [HSMul.hSMul, SMul.smul]
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  add_comm f g := by ext; simp only [add_def, add_comm]
/-
**PolynomialLaw.** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R (M →ₚₗ[R] N) where
  smul_zero a := rfl
  smul_add a f g := by ext; simp only [smul_def, add_def, smul_add]
  add_smul := add_smul
  zero_smul := zero_smul

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]
  (f : M →ₚₗ[R] N)

/-- The opposite of a polynomial law -/
/-
**PolynomialLaw.neg** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialLaw`。
形式化陈述：neg : M ->ₚₗ[R] N where toFun' S _ _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…

--- 原说明 ---
The opposite of a polynomial law
-/
noncomputable def neg : M →ₚₗ[R] N where
  toFun' S _ _ := (-1 : R) • f.toFun' S
/-
**PolynomialLaw.** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (M →ₚₗ[R] N) := ⟨neg⟩

@[simp]
/-
**PolynomialLaw.neg_def** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：neg_def (S : Type u) [CommSemiring S] [Algebra R S] : (-f).toFun' S = (-1 
: R) • f.toFun' S
参数：S : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
-/
theorem neg_def (S : Type u) [CommSemiring S] [Algebra R S] :
    (-f).toFun' S = (-1 : R) • f.toFun' S := rfl
/-
**PolynomialLaw.** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (M →ₚₗ[R] N) where
  zsmul n f := (n : R) • f
  zsmul_zero' f := by simp_rw [HSMul.hSMul, SMul.smul]; simp only [Int.cast_zero, zero_smul]
  zsmul_succ' n f := by
    simp_rw [HSMul.hSMul, SMul.smul]
    simp only [Nat.cast_succ, Int.cast_add, Int.cast_natCast, Int.cast_one, add_smul, one_smul]
  zsmul_neg' n f := by
    simp_rw [HSMul.hSMul, SMul.smul]
    ext S _ _ m
    rw [neg_def]
    simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev, add_smul,
      add_def_apply, smul_def_apply, Nat.succ_eq_add_one, Int.cast_add, Int.cast_natCast,
      Int.cast_one, one_smul, add_def, smul_def, Pi.smul_apply, Pi.add_apply, smul_add,
      smul_smul, neg_mul, one_mul]
    rw [add_comm]
  neg_add_cancel f := by
    ext S _ _ m
    simp only [add_def_apply, neg_def, Pi.smul_apply, zero_def, Pi.zero_apply]
    nth_rewrite 2 [← _root_.one_smul (M := R) (b := f.toFun' S m)]
    rw [← _root_.add_smul]
    simp only [neg_add_cancel, _root_.zero_smul]
  add_comm f g := by ext; simp only [add_def, add_comm]

end CommRing

end Module

section ground

variable {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N]
variable (f : M →ₚₗ[R] N)

/-- The map `M → N` associated with a `f : M →ₚₗ[R] N` (essentially, `f.toFun' R`) -/
/-
**PolynomialLaw.ground** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialLaw`。
形式化陈述：ground : M -> N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…

--- 原说明 ---
The map `M → N` associated with a `f : M →ₚₗ[R] N` (essentially, `f.toFun' R`)
-/
def ground : M → N := (TensorProduct.lid R N) ∘ (f.toFun' R) ∘ (TensorProduct.lid R M).symm
/-
**PolynomialLaw.ground_apply** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：ground_apply (m : M) : f.ground m = TensorProduct.lid R N (f.toFun' R (1 o
timesₜ[R] m))
参数：m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ground_apply (m : M) : f.ground m = TensorProduct.lid R N (f.toFun' R (1 ⊗ₜ[R] m)) := rfl
/-
**PolynomialLaw.** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (M →ₚₗ[R] N) (fun _ ↦ M → N) where
  coe := ground
/-
**PolynomialLaw.one_tmul_ground_apply'** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`
。
形式化陈述：one_tmul_ground_apply' {S : Type u} [CommSemiring S] [Algebra R S] (x : M)
 : 1 otimesₜ (f.ground x) = (f.toFun' S) (1 otimesₜ x)
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolynomialLaw.ground_apply`：ground_apply (m : M) : f.ground m = TensorPr
oduct.lid R N (f.toFun' R (1 otimesₜ[R] m))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `TensorProduct.includeRight_lid`：includeRight_lid {S : Type*} [Semiring S
] [Algebra R S] (m : R otimes[R] M) : (1 : S) otimesₜ[R] (TensorProduct.lid R M)
 m = (LinearMap.rTen…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.rTensor_tmul`：rTensor_tmul (m : M) (n : N) : f.rTensor M (n ot
imesₜ m) = f n otimesₜ m
· 使用定理 `AlgHom.toLinearMap_apply`：toLinearMap_apply (p : A) : φ.toLinearMap p = 
φ p
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `PolynomialLaw.isCompat_apply'`：PolynomialLaw.isCompat_apply' {R : Type u
} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M] {N : Type*} [AddCo
mmMonoid N] [Module…
-/
theorem one_tmul_ground_apply' {S : Type u} [CommSemiring S] [Algebra R S] (x : M) :
    1 ⊗ₜ (f.ground x) = (f.toFun' S) (1 ⊗ₜ x) := by
  rw [ground_apply]
  convert! f.isCompat_apply' (Algebra.algHom R R S) (1 ⊗ₜ[R] x)
  · simp only [includeRight_lid]
  · rw [rTensor_tmul, toLinearMap_apply, map_one]

/-- The map ground assigning a function `M → N` to a polynomial map `f : M →ₚₗ[R] N` as a
  linear map. -/
/-
**PolynomialLaw.lground** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialLaw`。
形式化陈述：lground : (M ->ₚₗ[R] N) ->ₗ[R] (M -> N) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map ground assigning a function `M → N` to a polynomial map `f : M →ₚₗ[R] N`
 as a
  linear map.
-/
def lground : (M →ₚₗ[R] N) →ₗ[R] (M → N) where
  toFun := ground
  map_add' x y := by ext m; simp [ground]
  map_smul' r x := by ext m; simp [ground]
/-
**PolynomialLaw.ground_id** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：ground_id : (id : M ->ₚₗ[R] M).ground = _root_.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ground_id : (id : M →ₚₗ[R] M).ground = _root_.id := by
  ext; simp [ground_apply, id_apply']
/-
**PolynomialLaw.ground_id_apply** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：ground_id_apply (m : M) : (id : M ->ₚₗ[R] M).ground m = m
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolynomialLaw.ground_id`：ground_id : (id : M ->ₚₗ[R] M).ground = _root_.
id
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
-/
theorem ground_id_apply (m : M) : (id : M →ₚₗ[R] M).ground m = m := by
  rw [ground_id, id_eq]

end ground

section Composition

variable {R : Type u} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {P : Type*} [AddCommMonoid P] [Module R P]
variable {Q : Type*} [AddCommMonoid Q] [Module R Q]
variable (f : M →ₚₗ[R] N) (g : N →ₚₗ[R] P) (h : P →ₚₗ[R] Q)

/-- Composition of polynomial maps. -/
/-
**PolynomialLaw.comp** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialLaw`。
形式化陈述：comp (g : N ->ₚₗ[R] P) (f : M ->ₚₗ[R] N) : M ->ₚₗ[R] P where toFun' S _ _
参数：g : N ->ₚₗ[R] P；f : M ->ₚₗ[R] N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…

--- 原说明 ---
Composition of polynomial maps.
-/
def comp (g : N →ₚₗ[R] P) (f : M →ₚₗ[R] N) : M →ₚₗ[R] P where
  toFun' S _ _ := (g.toFun' S).comp (f.toFun' S)
  isCompat' φ := by ext; simp only [Function.comp_apply, isCompat_apply']
/-
**PolynomialLaw.comp_toFun'** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：comp_toFun' (S : Type u) [CommSemiring S] [Algebra R S] : (g.comp f).toFun
' S = (g.toFun' S).comp (f.toFun' S)
参数：S : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
-/
theorem comp_toFun' (S : Type u) [CommSemiring S] [Algebra R S] :
    (g.comp f).toFun' S = (g.toFun' S).comp (f.toFun' S) := rfl
/-
**PolynomialLaw.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：comp_assoc : h.comp (g.comp f) = (h.comp g).comp f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc : h.comp (g.comp f) = (h.comp g).comp f := rfl
/-
**PolynomialLaw.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：comp_id : g.comp id = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.ext`：∀ {R : Type u} {inst : CommSemiring R} {M : Type u_1}
 {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   {N : Type u_2} {inst_
3 : Add…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
-/
theorem comp_id : g.comp id = g := by ext; rfl
/-
**PolynomialLaw.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：id_comp : id.comp f = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.ext`：∀ {R : Type u} {inst : CommSemiring R} {M : Type u_1}
 {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   {N : Type u_2} {inst_
3 : Add…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
-/
theorem id_comp : id.comp f = f := by ext; rfl

end Composition

section Universe

open scoped TensorProduct

open MvPolynomial

variable (R : Type u) [CommSemiring R]
  (M : Type*) [AddCommMonoid M] [Module R M]
  (N : Type*) [AddCommMonoid N] [Module R N]
  (S : Type v) [CommSemiring S] [Algebra R S]
  (f : M →ₚₗ[R] N)

section Lift

open LinearMap

-- The universe of `PolynomialLaw.lifts` is computed by the compiler
/-- The type of lifts of  `S ⊗[R] M` to a polynomial ring. -/
/-
**PolynomialLaw.lifts** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialLaw`。
形式化陈述：lifts : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of lifts of  `S ⊗[R] M` to a polynomial ring.
-/
def lifts : Type _ := Σ (s : Finset S), (MvPolynomial (Fin s.card) R) ⊗[R] M


variable {S}

/-- The lift of `f.toFun` to the type `lifts` -/
/-
**PolynomialLaw.** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lift of `f.toFun` to the type `lifts`
-/
def φ (s : Finset S) : MvPolynomial (Fin s.card) R →ₐ[R] S :=
  aeval (R := R) (fun n ↦ (s.equivFin.symm n : S))
/-
**PolynomialLaw.range_** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_φ (s : Finset S) : (φ R s).range = Algebra.adjoin R s := by
  simp only [φ]
  rw [← Algebra.adjoin_range_eq_range_aeval]
  congr
  rw [← Function.comp_def, Set.range_comp]
  simp only [Equiv.range_eq_univ, Set.image_univ, Subtype.range_coe_subtype, Finset.setOfPred_mem]

variable (S)

/-- The projection from `φ` to `S ⊗[R] M`. -/
/-
**PolynomialLaw.** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection from `φ` to `S ⊗[R] M`.
-/
def π : lifts R M S → S ⊗[R] M := fun ⟨s, p⟩ ↦ rTensor M (φ R s).toLinearMap p

variable {R M N}

/-- The auxiliary lift of `PolynomialLaw.toFun'` on `PolynomialLaw.lifts` -/
/-
**PolynomialLaw.toFunLifted** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialLaw`。
形式化陈述：toFunLifted : lifts R M S -> S otimes[R] N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…

--- 原说明 ---
The auxiliary lift of `PolynomialLaw.toFun'` on `PolynomialLaw.lifts`
-/
def toFunLifted : lifts R M S → S ⊗[R] N :=
  fun ⟨s, p⟩ ↦ rTensor N (φ R s).toLinearMap (f.toFun' (MvPolynomial (Fin s.card) R) p)

/-- The extension of `PolynomialLaw.toFun'` to all universes. -/
/-
**PolynomialLaw.toFun** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialLaw`。
形式化陈述：toFun : S otimes[R] M -> S otimes[R] N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension of `PolynomialLaw.toFun'` to all universes.
-/
def toFun : S ⊗[R] M → S ⊗[R] N := Function.extend (π R M S) (f.toFunLifted S) (fun _ ↦ 0)

variable {S}
/-
**PolynomialLaw.exists_range_** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_range_φ_eq_of_fg {B : Subalgebra R S} (hB : Subalgebra.FG B) :
    ∃ s : Finset S, (φ R s).range = B :=
  ⟨hB.choose, by simp only [range_φ, hB.choose_spec]⟩

section diagrams

variable
    {A : Type u} [CommSemiring A] [Algebra R A] {φ : A →ₐ[R] S} (p : A ⊗[R] M)
    {T : Type w} [CommSemiring T] [Algebra R T]
    {B : Type u} [CommSemiring B] [Algebra R B] {ψ : B →ₐ[R] T} (q : B ⊗[R] M)
    (g : A →ₐ[R] B) (h : S →ₐ[R] T)

/-- Compare the values of `PolynomialLaw.toFun'` in a square diagram -/
/-
**PolynomialLaw.toFun'_eq_of_diagram** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {M : Type u_1} [inst_1 : AddCommMon
oid M] [inst_2 : _root_.Module R M]   {N : Type u_2} [inst_3 : AddCommMonoid N] 
[inst_4 : _root_.Module R N] {S : Type v} [inst_5 : CommSemiring S]   [inst_6 : 
Algebra R S] (f : M →ₚₗ[R] N) {A : Type u} [inst_7 : CommSemiring A] [inst_8 : A
lgebra R A] {φ : A →ₐ[R] S}   (p : TensorProduct R A M) {T : Type w} [inst_9 : C
ommSemiring T] [inst_10 : Algebra R T] {B : Type u}   [inst_11 : CommSemiring B]
 [inst_12 : Algebra R B] {ψ : B →ₐ[R] T} (q : TensorProduct R B M) (h : S →ₐ[R] 
T)   (h' : ↥φ.range →ₐ[R] ↥ψ.range),   ψ.range.val.comp h' = h.comp φ.range.val 
→     (LinearMap.rTensor M (h'.comp φ.rangeRestrict).toLinearMap) p =         (L
inearMap.rTensor M ψ.rangeRestrict.toLinearMap) q →       (LinearMap.rTensor N (
h.comp φ).toLinearMap) (f.toFun' A p) = (LinearMap.rTensor N ψ.toLinearMap) (f.t
oFun' B q)
参数：f : M →ₚₗ[R] N；p : TensorProduct R A M；q : TensorProduct R B M；h : S →ₐ[R] T；
h' : ↥φ.range →ₐ[R] ↥ψ.range；LinearMap.rTensor M (h'.comp φ.rangeRestrict).toLin
earMap；LinearMap.rTensor M ψ.rangeRestrict.toLinearMap；LinearMap.rTensor N (h.co
mp φ).toLinearMap；f.toFun' A p；LinearMap.rTensor N ψ.toLinearMap；f.toFun' B q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgEquiv.comp_symm`：comp_symm (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp (e : A₁ ->
ₐ[R] A₂) ↑e.symm = AlgHom.id R A₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
· 使用定理 `AlgHom.val_comp_rangeRestrict`：val_comp_rangeRestrict : (Subalgebra.val 
_).comp φ.rangeRestrict = φ
· 使用定理 `RingCon.quotientKerEquivRangeₐ_comp_mkₐ`：quotientKerEquivRangeₐ_comp_mkₐ
 (φ : M ->ₐ[R] N) : ((quotientKerEquivRangeₐ φ).toAlgHom.comp ((ker (φ : M ->+* 
N)).mkₐ R)) = φ.rangeRestrict
· 使用定理 `AlgHom.comp_assoc`：comp_assoc (φ₁ : C ->ₐ[R] D) (φ₂ : B ->ₐ[R] C) (φ₃ : 
A ->ₐ[R] B) : (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.rTensor_comp_apply`：rTensor_comp_apply (x : N otimes[R] M) : (
g.comp f).rTensor M x = (g.rTensor M) ((f.rTensor M) x)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `AlgHom.comp_toLinearMap`：comp_toLinearMap (f : A ->ₐ[R] B) (g : B ->ₐ[R]
 C) : (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap
· 使用定理 `PolynomialLaw.isCompat_apply'`：PolynomialLaw.isCompat_apply' {R : Type u
} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M] {N : Type*} [AddCo
mmMonoid N] [Module…
· 使用定理 `AlgEquiv.symm_comp`：symm_comp (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp ↑e.symm (e
 : A₁ ->ₐ[R] A₂) = AlgHom.id R A₁

--- 原说明 ---
Compare the values of `PolynomialLaw.toFun'` in a square diagram
-/
theorem toFun'_eq_of_diagram
    (h : S →ₐ[R] T) (h' : φ.range →ₐ[R] ψ.range)
    (hh' : ψ.range.val.comp h' = h.comp φ.range.val)
    (hpq : (h'.comp φ.rangeRestrict).toLinearMap.rTensor M p =
      ψ.rangeRestrict.toLinearMap.rTensor M q) :
    (h.comp φ).toLinearMap.rTensor N (f.toFun' A p) =
      ψ.toLinearMap.rTensor N (f.toFun' B q) := by
  let θ := (quotientKerEquivRangeₐ (R := R) ψ).symm.toAlgHom.comp
    (h'.comp (quotientKerEquivRangeₐ φ).toAlgHom)
  have ht : (h.comp φ.range.val).comp (quotientKerEquivRangeₐ φ).toAlgHom =
      ψ.range.val.comp ((quotientKerEquivRangeₐ ψ).toAlgHom.comp θ) := by
    simp only [θ, ← AlgHom.comp_assoc, ← hh']
    simp [AlgHom.comp_assoc]
  rw [← φ.val_comp_rangeRestrict, ← quotientKerEquivRangeₐ_comp_mkₐ φ,
    ← ψ.val_comp_rangeRestrict, ← quotientKerEquivRangeₐ_comp_mkₐ ψ,
    ← AlgHom.comp_assoc, ← AlgHom.comp_assoc _, ht]
  simp only [AlgHom.comp_toLinearMap, rTensor_comp_apply]
  apply congr_arg
  rw [← rTensor_comp_apply, ← AlgHom.comp_toLinearMap, isCompat_apply',
    isCompat_apply', AlgHom.comp_toLinearMap, rTensor_comp_apply,
    isCompat_apply']
  apply congr_arg
  simp only [θ, ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap, AlgHom.comp_assoc]
  rw [quotientKerEquivRangeₐ_comp_mkₐ, comp_toLinearMap,
    rTensor_comp_apply, hpq, ← rTensor_comp_apply, ← comp_toLinearMap,
    ← quotientKerEquivRangeₐ_comp_mkₐ, ← AlgHom.comp_assoc]
  simp

/-- Compare the values of `PolynomialLaw.toFun'` in a square diagram,
  when one of the maps is a subalgebra inclusion. -/
/-
**PolynomialLaw.toFun'_eq_of_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`
。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {M : Type u_1} [inst_1 : AddCommMon
oid M] [inst_2 : _root_.Module R M]   {N : Type u_2} [inst_3 : AddCommMonoid N] 
[inst_4 : _root_.Module R N] {S : Type v} [inst_5 : CommSemiring S]   [inst_6 : 
Algebra R S] (f : M →ₚₗ[R] N) {A : Type u} [inst_7 : CommSemiring A] [inst_8 : A
lgebra R A] {φ : A →ₐ[R] S}   (p : TensorProduct R A M) {B : Type u} [inst_9 : C
ommSemiring B] [inst_10 : Algebra R B] (q : TensorProduct R B M)   {ψ : B →ₐ[R] 
S} (h : φ.range ≤ ψ.range),   (LinearMap.rTensor M ((Subalgebra.inclusion h).com
p φ.rangeRestrict).toLinearMap) p =       (LinearMap.rTensor M ψ.rangeRestrict.t
oLinearMap) q →     (LinearMap.rTensor N φ.toLinearMap) (f.toFun' A p) = (Linear
Map.rTensor N ψ.toLinearMap) (f.toFun' B q)
参数：f : M →ₚₗ[R] N；p : TensorProduct R A M；q : TensorProduct R B M；h : φ.range ≤ 
ψ.range；LinearMap.rTensor M ((Subalgebra.inclusion h).comp φ.rangeRestrict).toLi
nearMap；LinearMap.rTensor M ψ.rangeRestrict.toLinearMap；LinearMap.rTensor N φ.to
LinearMap；f.toFun' A p；LinearMap.rTensor N ψ.toLinearMap；f.toFun' B q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.toFun'_eq_of_diagram`：∀ {R : Type u} [inst : CommSemiring 
R] {M : Type u_1} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N :
 Type u_2} [inst_3 : Add…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Compare the values of `PolynomialLaw.toFun'` in a square diagram,
  when one of the maps is a subalgebra inclusion.
-/
theorem toFun'_eq_of_inclusion {ψ : B →ₐ[R] S} (h : φ.range ≤ ψ.range)
    (hpq : ((Subalgebra.inclusion h).comp
      φ.rangeRestrict).toLinearMap.rTensor M p = ψ.rangeRestrict.toLinearMap.rTensor M q) :
    φ.toLinearMap.rTensor N (f.toFun' A p) = ψ.toLinearMap.rTensor N (f.toFun' B q) :=
  toFun'_eq_of_diagram f p q (AlgHom.id R S) (Subalgebra.inclusion h) (by ext x; simp) hpq

end diagrams

/-
**PolynomialLaw.factorsThrough_toFunLifted_** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
lLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem factorsThrough_toFunLifted_π :
    Function.FactorsThrough (f.toFunLifted S) (π R M S) := by
  rintro ⟨s, p⟩ ⟨s', p'⟩ h
  simp only [toFunLifted]
  set u := rTensor M (φ R s).rangeRestrict.toLinearMap p with hu
  have uFG : Subalgebra.FG (R := R) (φ R s).range := by
    rw [← Algebra.map_top]
    exact Subalgebra.FG.map _ Algebra.FiniteType.out
  set u' := rTensor M (φ R s').rangeRestrict.toLinearMap p' with hu'
  have u'FG : Subalgebra.FG (R := R) (φ R s').range := by
    rw [← Algebra.map_top]
    exact Subalgebra.FG.map _ Algebra.FiniteType.out
  have huu' : rTensor M (Subalgebra.val _).toLinearMap u =
    rTensor M (Subalgebra.val _).toLinearMap u' := by
    simp only [π] at h
    simp only [hu, hu', ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap,
      val_comp_rangeRestrict, h]
  obtain ⟨B, hAB, hA'B, ⟨t, hB⟩, h⟩ :=
    TensorProduct.Algebra.eq_of_fg_of_subtype_eq' (R := R) uFG u'FG huu'
  rw [← range_φ R t, eq_comm] at hB
  have hAB' : (φ R s).range ≤ (φ R t).range := le_trans hAB (le_of_eq hB)
  have hA'B' : (φ R s').range ≤ (φ R t).range := le_trans hA'B (le_of_eq hB)
  have : ∃ q : MvPolynomial (Fin t.card) R ⊗[R] M, rTensor M (toLinearMap (φ R t).rangeRestrict) q =
      rTensor M ((Subalgebra.inclusion (le_of_eq hB)).comp
        (Subalgebra.inclusion hAB)).toLinearMap u :=
    rTensor_surjective _ (rangeRestrict_surjective _) _
  obtain ⟨q, hq⟩ := this
  rw [toFun'_eq_of_inclusion f p q hAB', toFun'_eq_of_inclusion f p' q hA'B']
  · simp only [hq, comp_toLinearMap, rTensor_comp, LinearMap.comp_apply]
    rw [← hu', h]
    simp only [← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap]
    rfl
  · simp only [hq, hu, ← LinearMap.comp_apply, comp_toLinearMap, rTensor_comp]
    congr; ext; rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**PolynomialLaw.toFun_eq_rTensor_** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_rTensor_φ_toFun' {t : S ⊗[R] M} {s : Finset S}
    {p : MvPolynomial (Fin s.card) R ⊗[R] M} (ha : π R M S (⟨s, p⟩ : lifts R M S) = t) :
    f.toFun S t = (φ R s).toLinearMap.rTensor N (f.toFun' _ p) := by
  rw [PolynomialLaw.toFun, ← ha, (factorsThrough_toFunLifted_π f).extend_apply, toFunLifted]
/-
**PolynomialLaw.exists_lift_of_mem_range_rTensor** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomialLaw`。
形式化陈述：exists_lift_of_mem_range_rTensor {T : Type*} [CommSemiring T] [Algebra R T
] (A : Subalgebra R T) {φ : S ->ₐ[R] T} (hφ : A <= φ.range) {t : T otimes[R] M} 
(ht : t in range ((Subalgebra.val A).toLinearMap.rTensor M)) : exists s : S otim
es[R] M, φ.toLinearMap.rTensor M s = t
参数：A : Subalgebra R T；hφ : A <= φ.range；ht : t in range ((Subalgebra.val A).toLi
nearMap.rTensor M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.rTensor_surjective`：LinearMap.rTensor_surjective (hg : Functio
n.Surjective g) : Function.Surjective (rTensor Q g)
· 使用定理 `AlgHom.rangeRestrict_surjective`：rangeRestrict_surjective (f : A ->ₐ[R] 
B) : Function.Surjective (f.rangeRestrict)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.val_comp_inclusion`：val_comp_inclusion (hst : S <= T) : T.val
.comp (inclusion hst) = S.val
· 使用定理 `AlgHom.comp_toLinearMap`：comp_toLinearMap (f : A ->ₐ[R] B) (g : B ->ₐ[R]
 C) : (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHom.val_comp_codRestrict`：val_comp_codRestrict (f : A ->ₐ[R] B) (S : 
Subalgebra R B) (hf : forall x, f x in S) : S.val.comp (f.codRestrict S hf) = f
· 使用定理 `AlgHom.mem_range_self`：mem_range_self (φ : A ->ₐ[R] B) (x : A) : φ x in 
φ.range
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_lift_of_mem_range_rTensor
    {T : Type*} [CommSemiring T] [Algebra R T]
    (A : Subalgebra R T) {φ : S →ₐ[R] T} (hφ : A ≤ φ.range) {t : T ⊗[R] M}
    (ht : t ∈ range ((Subalgebra.val A).toLinearMap.rTensor M)) :
    ∃ s : S ⊗[R] M, φ.toLinearMap.rTensor M s = t := by
  obtain ⟨u, hu⟩ := ht
  suffices h_surj : Function.Surjective ((φ.rangeRestrict.toLinearMap).rTensor M) by
    obtain ⟨p, hp⟩ := h_surj ((Subalgebra.inclusion hφ).toLinearMap.rTensor M u)
    use p
    rw [← hu, ← Subalgebra.val_comp_inclusion hφ, comp_toLinearMap, rTensor_comp,
      LinearMap.comp_apply, ← hp, ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap]
    simp
  exact rTensor_surjective M (rangeRestrict_surjective φ)

/-- Tensor products in `S ⊗[R] M` can be lifted to some
`MvPolynomial R n ⊗[R] M`, for a finite `n`. -/
/-
**PolynomialLaw.** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensor products in `S ⊗[R] M` can be lifted to some
`MvPolynomial R n ⊗[R] M`, for a finite `n`.
-/
theorem π_surjective : Function.Surjective (π R M S) := by
  intro t
  obtain ⟨B : Subalgebra R S, hB : B.FG, ht : t ∈ range _⟩ := TensorProduct.Algebra.exists_of_fg t
  obtain ⟨s : Finset S, hs : (PolynomialLaw.φ R s).range = B⟩ := exists_range_φ_eq_of_fg hB
  obtain ⟨p, hp⟩ := exists_lift_of_mem_range_rTensor B (le_of_eq hs.symm) ht
  exact ⟨⟨s, p⟩, hp⟩

/-- Lift an element of a tensor product -/
/-
**PolynomialLaw.exists_lift** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：exists_lift (t : S otimes[R] M) : exists (n : Nat) (ψ : MvPolynomial (Fin 
n) R ->ₐ[R] S) (p : MvPolynomial (Fin n) R otimes[R] M), ψ.toLinearMap.rTensor M
 p = t
参数：t : S otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.π_surjective`：π_surjective : Function.Surjective (π R M S)

--- 原说明 ---
Lift an element of a tensor product
-/
theorem exists_lift (t : S ⊗[R] M) : ∃ (n : ℕ) (ψ : MvPolynomial (Fin n) R →ₐ[R] S)
    (p : MvPolynomial (Fin n) R ⊗[R] M), ψ.toLinearMap.rTensor M p = t := by
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  use s.card, φ R s, p, ha

/-- Lift an element of a tensor product and a scalar -/
/-
**PolynomialLaw.exists_lift'** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：exists_lift' (t : S otimes[R] M) (s : S) : exists (n : Nat) (ψ : MvPolynom
ial (Fin n) R ->ₐ[R] S) (p : MvPolynomial (Fin n) R otimes[R] M) (q : MvPolynomi
al (Fin n) R), ψ.toLinearMap.rTensor M p = t ∧ ψ q = s
参数：t : S otimes[R] M；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.Algebra.exists_of_fg`：TensorProduct.Algebra.exists_of_fg :
 exists (A : Subalgebra R S), Subalgebra.FG A ∧ u in range (rTensor N A.val.toLi
nearMap)
· 使用定理 `Subalgebra.FG.sup`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [
inst_1 : Semiring A] [inst_2 : Algebra R A]   {S S' : Subalgebra R A}, S.FG → S'
.FG → (…
· 使用定理 `Subalgebra.fg_adjoin_finset`：fg_adjoin_finset (s : Finset A) : (Algebra.
adjoin R (↑s : Set A)).FG
· 使用定理 `PolynomialLaw.exists_range_φ_eq_of_fg`：exists_range_φ_eq_of_fg {B : Suba
lgebra R S} (hB : Subalgebra.FG B) : exists s : Finset S, (φ R s).range = B
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `PolynomialLaw.exists_lift_of_mem_range_rTensor`：exists_lift_of_mem_range
_rTensor {T : Type*} [CommSemiring T] [Algebra R T] (A : Subalgebra R T) {φ : S 
->ₐ[R] T} (hφ : A <= φ.range) {t : T…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose

--- 原说明 ---
Lift an element of a tensor product and a scalar
-/
theorem exists_lift' (t : S ⊗[R] M) (s : S) : ∃ (n : ℕ) (ψ : MvPolynomial (Fin n) R →ₐ[R] S)
    (p : MvPolynomial (Fin n) R ⊗[R] M) (q : MvPolynomial (Fin n) R),
      ψ.toLinearMap.rTensor M p = t ∧ ψ q = s := by
  obtain ⟨A, hA, ht⟩ := TensorProduct.Algebra.exists_of_fg t
  have hB : Subalgebra.FG (A ⊔ Algebra.adjoin R ({s} : Finset S)) :=
    Subalgebra.FG.sup hA (Subalgebra.fg_adjoin_finset _)
  obtain ⟨gen, hgen⟩ := exists_range_φ_eq_of_fg hB
  have hAB : A ≤ A ⊔ Algebra.adjoin R ({s} : Finset S) := le_sup_left
  rw [← hgen] at hAB
  obtain ⟨p, hp⟩ := exists_lift_of_mem_range_rTensor _ hAB ht
  have hs : s ∈ (φ R gen).range := by
    rw [hgen]
    apply Algebra.subset_adjoin
    simp only [Finset.coe_singleton, Set.sup_eq_union, Set.mem_union, SetLike.mem_coe]
    exact Or.inr (Algebra.subset_adjoin rfl)
  use gen.card, φ R gen, p, hs.choose, hp, hs.choose_spec

/-- For semirings in the universe `u`, `PolynomialLaw.toFun` coincides
with `PolynomialLaw.toFun'`. -/
@[simp]
/-
**PolynomialLaw.toFun'_eq_toFun** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {M : Type u_1} [inst_1 : AddCommMon
oid M] [inst_2 : _root_.Module R M]   {N : Type u_2} [inst_3 : AddCommMonoid N] 
[inst_4 : _root_.Module R N] (f : M →ₚₗ[R] N) (S : Type u)   [inst_5 : CommSemir
ing S] [inst_6 : Algebra R S], f.toFun' S = PolynomialLaw.toFun S f
参数：f : M →ₚₗ[R] N；S : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
· 使用定理 `PolynomialLaw.π_surjective`：π_surjective : Function.Surjective (π R M S)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PolynomialLaw.toFun_eq_rTensor_φ_toFun'`：toFun_eq_rTensor_φ_toFun' {t : 
S otimes[R] M} {s : Finset S} {p : MvPolynomial (Fin s.card) R otimes[R] M} (ha 
: π R M S (⟨s, p⟩ : lifts R M…
· 使用定理 `PolynomialLaw.isCompat_apply'`：PolynomialLaw.isCompat_apply' {R : Type u
} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M] {N : Type*} [AddCo
mmMonoid N] [Module…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
For semirings in the universe `u`, `PolynomialLaw.toFun` coincides
with `PolynomialLaw.toFun'`.
-/
theorem toFun'_eq_toFun (S : Type u) [CommSemiring S] [Algebra R S] :
    f.toFun' S = f.toFun S := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [f.toFun_eq_rTensor_φ_toFun' ha, f.isCompat_apply']
  exact congr_arg _ ha.symm

/-- Extends `PolynomialLaw.isCompat_apply'` to all universes. -/
/-
**PolynomialLaw.isCompat_apply** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：isCompat_apply {T : Type w} [CommSemiring T] [Algebra R T] (h : S ->ₐ[R] T
) (t : S otimes[R] M) : rTensor N h.toLinearMap (f.toFun S t) = f.toFun T (rTens
or M h.toLinearMap t)
参数：h : S ->ₐ[R] T；t : S otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.π_surjective`：π_surjective : Function.Surjective (π R M S)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolynomialLaw.range_φ`：range_φ (s : Finset S) : (φ R s).range = Algebra.
adjoin R s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Algebra.adjoin_image`：adjoin_image (f : A ->ₐ[R] B) (s : Set A) : adjoin
 R (f '' s) = (adjoin R s).map f
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.aeval_rename`：aeval_rename [Algebra R S] : aeval g (rename 
k p) = aeval (g ∘ k) p
· 使用定理 `MvPolynomial.comp_aeval`：comp_aeval {B : Type*} [CommSemiring B] [Algebr
a R B] (φ : S₁ ->ₐ[R] B) : φ.comp (aeval f) = aeval fun i => φ (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
· 使用定理 `PolynomialLaw.toFun_eq_rTensor_φ_toFun'`：toFun_eq_rTensor_φ_toFun' {t : 
S otimes[R] M} {s : Finset S} {p : MvPolynomial (Fin s.card) R otimes[R] M} (ha 
: π R M S (⟨s, p⟩ : lifts R M…
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
· 使用定理 `AlgHom.comp_toLinearMap`：comp_toLinearMap (f : A ->ₐ[R] B) (g : B ->ₐ[R]
 C) : (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap
· 使用定理 `PolynomialLaw.toFun'_eq_of_diagram`：∀ {R : Type u} [inst : CommSemiring 
R] {M : Type u_1} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N :
 Type u_2} [inst_3 : Add…
· 使用定理 `AlgHom.val_comp_codRestrict`：val_comp_codRestrict (f : A ->ₐ[R] B) (S : 
Subalgebra R B) (hf : forall x, f x in S) : S.val.comp (f.codRestrict S hf) = f
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s

--- 原说明 ---
Extends `PolynomialLaw.isCompat_apply'` to all universes.
-/
theorem isCompat_apply {T : Type w} [CommSemiring T] [Algebra R T] (h : S →ₐ[R] T) (t : S ⊗[R] M) :
    rTensor N h.toLinearMap (f.toFun S t) = f.toFun T (rTensor M h.toLinearMap t) := by
  classical
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  let s' := s.image h
  let h' : (φ R s).range →ₐ[R] (φ R s').range :=
    (h.comp (Subalgebra.val _)).codRestrict (φ R s').range (by
    rintro ⟨x, hx⟩
    simp only [range_φ] at hx ⊢
    simp only [AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply, Finset.coe_image,
      Algebra.adjoin_image, s']
    exact ⟨x, hx, rfl⟩)
  let j : Fin s.card → Fin s'.card :=
    (s'.equivFin) ∘ (fun ⟨x, hx⟩ ↦ ⟨h x, Finset.mem_image_of_mem h hx⟩) ∘ (s.equivFin).symm
  have eq_h_comp : (φ R s').comp (rename j) = h.comp (φ R s) := by
    ext p
    simp only [φ, AlgHom.comp_apply, aeval_rename, comp_aeval]
    congr
    ext n
    simp only [Function.comp_apply, Equiv.symm_apply_apply, j]
  let p' := rTensor M (rename j).toLinearMap p
  have ha' : π R M T (⟨s', p'⟩ : lifts R M T) = rTensor M h.toLinearMap t := by
    simp only [← ha, π, p', ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap, eq_h_comp]
  rw [toFun_eq_rTensor_φ_toFun' f ha, toFun_eq_rTensor_φ_toFun' f ha', ← LinearMap.comp_apply,
    ← rTensor_comp, ← comp_toLinearMap]
  apply toFun'_eq_of_diagram f p p' h h'
  · simp only [val_comp_codRestrict, h']
  · simp only [p', ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap]
    congr
    ext n
    simp only [AlgHom.coe_comp, Function.comp_apply, coe_codRestrict,
      Subalgebra.coe_val, rename_X, h', j]
    simp only [φ, aeval_X, Equiv.symm_apply_apply]

/-- Extends `PolynomialLaw.isCompat` to all universes -/
/-
**PolynomialLaw.isCompat** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：isCompat {T : Type w} [CommSemiring T] [Algebra R T] (h : S ->ₐ[R] T) : h.
toLinearMap.rTensor N ∘ f.toFun S = f.toFun T ∘ h.toLinearMap.rTensor M
参数：h : S ->ₐ[R] T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolynomialLaw.isCompat_apply`：isCompat_apply {T : Type w} [CommSemiring 
T] [Algebra R T] (h : S ->ₐ[R] T) (t : S otimes[R] M) : rTensor N h.toLinearMap 
(f.toFun S t) = f.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Extends `PolynomialLaw.isCompat` to all universes
-/
theorem isCompat {T : Type w} [CommSemiring T] [Algebra R T] (h : S →ₐ[R] T) :
    h.toLinearMap.rTensor N ∘ f.toFun S = f.toFun T ∘ h.toLinearMap.rTensor M := by
  ext t
  simp only [Function.comp_apply, PolynomialLaw.isCompat_apply]

end Lift

section Module

variable
  {R : Type u} [CommSemiring R]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N]
  (r a b : R) (f g : M →ₚₗ[R] N)
  {S : Type*} [CommSemiring S] [Algebra R S]

/-- Extension of `PolynomialLaw.zero_def` -/
@[simp]
/-
**PolynomialLaw.toFun_zero** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：toFun_zero : (0 : M ->ₚₗ[R] N).toFun S = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PolynomialLaw.π_surjective`：π_surjective : Function.Surjective (π R M S)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
· 使用定理 `PolynomialLaw.toFun_eq_rTensor_φ_toFun'`：toFun_eq_rTensor_φ_toFun' {t : 
S otimes[R] M} {s : Finset S} {p : MvPolynomial (Fin s.card) R otimes[R] M} (ha 
: π R M S (⟨s, p⟩ : lifts R M…
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Extension of `PolynomialLaw.zero_def`
-/
theorem toFun_zero : (0 : M →ₚₗ[R] N).toFun S = 0 := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_rTensor_φ_toFun' _ ha, zero_def, Pi.zero_apply, _root_.map_zero]

/-- Extension of `PolynomialLaw.add_def_apply` -/
@[simp]
/-
**PolynomialLaw.toFun_add_apply** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：toFun_add_apply (t : S otimes[R] M) : (f + g).toFun S t = f.toFun S t + g.
toFun S t
参数：t : S otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialLaw.π_surjective`：π_surjective : Function.Surjective (π R M S)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolynomialLaw.toFun_eq_rTensor_φ_toFun'`：toFun_eq_rTensor_φ_toFun' {t : 
S otimes[R] M} {s : Finset S} {p : MvPolynomial (Fin s.card) R otimes[R] M} (ha 
: π R M S (⟨s, p⟩ : lifts R M…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Extension of `PolynomialLaw.add_def_apply`
-/
theorem toFun_add_apply (t : S ⊗[R] M) :
    (f + g).toFun S t = f.toFun S t + g.toFun S t := by
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [Pi.add_apply, toFun_eq_rTensor_φ_toFun' _ ha, add_def, map_add]

/-- Extension of `PolynomialLaw.add_def` -/
@[simp]
/-
**PolynomialLaw.toFun_add** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：toFun_add : (f + g).toFun S = f.toFun S + g.toFun S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolynomialLaw.toFun_add_apply`：toFun_add_apply (t : S otimes[R] M) : (f 
+ g).toFun S t = f.toFun S t + g.toFun S t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Extension of `PolynomialLaw.add_def`
-/
theorem toFun_add :
    (f + g).toFun S = f.toFun S + g.toFun S := by
  ext t
  simp only [Pi.add_apply, toFun_add_apply]

@[simp]
/-
**PolynomialLaw.toFun_neg** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：toFun_neg {R : Type u} [CommRing R] {M : Type*} [AddCommGroup M] [Module R
 M] {N : Type*} [AddCommGroup N] [Module R N] (f : M ->ₚₗ[R] N) (S : Type*) [Com
mSemiring S] [Algebra R S] : (-f).toFun S = (-1 : R) • (f.toFun S)
参数：f : M ->ₚₗ[R] N；S : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PolynomialLaw.π_surjective`：π_surjective : Function.Surjective (π R M S)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolynomialLaw.toFun_eq_rTensor_φ_toFun'`：toFun_eq_rTensor_φ_toFun' {t : 
S otimes[R] M} {s : Finset S} {p : MvPolynomial (Fin s.card) R otimes[R] M} (ha 
: π R M S (⟨s, p⟩ : lifts R M…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFun_neg {R : Type u} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₚₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S] :
    (-f).toFun S = (-1 : R) • (f.toFun S) := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_rTensor_φ_toFun' _ ha, neg_def, Pi.smul_apply, map_smul]

variable (S) in
/-- Extension of `PolynomialLaw.smul_def` -/
@[simp]
/-
**PolynomialLaw.toFun_smul** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：toFun_smul : (r • f).toFun S = r • (f.toFun S)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PolynomialLaw.π_surjective`：π_surjective : Function.Surjective (π R M S)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolynomialLaw.toFun_eq_rTensor_φ_toFun'`：toFun_eq_rTensor_φ_toFun' {t : 
S otimes[R] M} {s : Finset S} {p : MvPolynomial (Fin s.card) R otimes[R] M} (ha 
: π R M S (⟨s, p⟩ : lifts R M…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Extension of `PolynomialLaw.smul_def`
-/
theorem toFun_smul : (r • f).toFun S = r • (f.toFun S) := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_rTensor_φ_toFun' _ ha, smul_def, Pi.smul_apply, map_smul]

end Module

section ground

variable {R : Type u} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    {N : Type*} [AddCommMonoid N] [Module R N]
    (f : M →ₚₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S]

/-
**PolynomialLaw.one_tmul_ground** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：one_tmul_ground (x : M) : 1 otimesₜ f.ground x = f.toFun S (1 otimesₜ x)
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
· 使用定理 `PolynomialLaw.toFun'_eq_toFun`：∀ {R : Type u} [inst : CommSemiring R] {M
 : Type u_1} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Type
 u_2} [inst_3 : Add…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `TensorProduct.includeRight_lid`：includeRight_lid {S : Type*} [Semiring S
] [Algebra R S] (m : R otimes[R] M) : (1 : S) otimesₜ[R] (TensorProduct.lid R M)
 m = (LinearMap.rTen…
· 使用定理 `LinearMap.rTensor_tmul`：rTensor_tmul (m : M) (n : N) : f.rTensor M (n ot
imesₜ m) = f n otimesₜ m
· 使用定理 `AlgHom.toLinearMap_apply`：toLinearMap_apply (p : A) : φ.toLinearMap p = 
φ p
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `PolynomialLaw.isCompat_apply`：isCompat_apply {T : Type w} [CommSemiring 
T] [Algebra R T] (h : S ->ₐ[R] T) (t : S otimes[R] M) : rTensor N h.toLinearMap 
(f.toFun S t) = f.…
-/
theorem one_tmul_ground (x : M) :
    1 ⊗ₜ f.ground x = f.toFun S (1 ⊗ₜ x) := by
  simp only [ground, toFun'_eq_toFun]
  convert! f.isCompat_apply (Algebra.ofId R S) (1 ⊗ₜ[R] x)
  · simp only [Function.comp_apply, TensorProduct.lid_symm_apply, TensorProduct.includeRight_lid]
    congr
  · rw [rTensor_tmul, toLinearMap_apply, _root_.map_one]

end ground

section Comp

variable {R : Type u} [CommSemiring R]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N]
  {P : Type*} [AddCommMonoid P] [Module R P]
  {Q : Type*} [AddCommMonoid Q] [Module R Q]
  (f : M →ₚₗ[R] N) (g : N →ₚₗ[R] P) (h : P →ₚₗ[R] Q)

/-- Extension of `MvPolynomial.comp_toFun'` -/
@[simp]
/-
**PolynomialLaw.toFun_comp** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：toFun_comp (S : Type*) [CommSemiring S] [Algebra R S] : (g.comp f).toFun S
 = (g.toFun S).comp (f.toFun S)
参数：S : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PolynomialLaw.π_surjective`：π_surjective : Function.Surjective (π R M S)
· 使用定理 `PolynomialLaw.toFun'`：toFun'_eq_of_diagram (h : S ->ₐ[R] T) (h' : φ.rang
e ->ₐ[R] ψ.range) (hh' : ψ.range.val.comp h' = h.comp φ.range.val) (hpq : (h'.co
mp φ.range…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolynomialLaw.toFun_eq_rTensor_φ_toFun'`：toFun_eq_rTensor_φ_toFun' {t : 
S otimes[R] M} {s : Finset S} {p : MvPolynomial (Fin s.card) R otimes[R] M} (ha 
: π R M S (⟨s, p⟩ : lifts R M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `PolynomialLaw.comp_toFun'`：comp_toFun' (S : Type u) [CommSemiring S] [Al
gebra R S] : (g.comp f).toFun' S = (g.toFun' S).comp (f.toFun' S)

--- 原说明 ---
Extension of `MvPolynomial.comp_toFun'`
-/
theorem toFun_comp (S : Type*) [CommSemiring S] [Algebra R S] :
    (g.comp f).toFun S = (g.toFun S).comp (f.toFun S) := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  have hb : PolynomialLaw.π R N S ⟨s, f.toFun' _ p⟩ = f.toFun S t := by
    simp only [toFun_eq_rTensor_φ_toFun' _ ha, π]
  rw [Function.comp_apply, toFun_eq_rTensor_φ_toFun' _ hb, toFun_eq_rTensor_φ_toFun' _ ha,
    comp_toFun', Function.comp_apply]
/-
**PolynomialLaw.toFun_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialLaw`。
形式化陈述：toFun_comp_apply (S : Type*) [CommSemiring S] [Algebra R S] (m : S otimes[
R] M) : (g.comp f).toFun S m = (g.toFun S) (f.toFun S m)
参数：S : Type*；m : S otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PolynomialLaw.toFun_comp`：toFun_comp (S : Type*) [CommSemiring S] [Algeb
ra R S] : (g.comp f).toFun S = (g.toFun S).comp (f.toFun S)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFun_comp_apply (S : Type*) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    (g.comp f).toFun S m = (g.toFun S) (f.toFun S m) := by
  simp only [toFun_comp, Function.comp_apply]

end Comp

end Universe

end PolynomialLaw

