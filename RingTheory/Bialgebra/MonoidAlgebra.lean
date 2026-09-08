/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Yaël Dillies, Michał Mrugała
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.Bialgebra.GroupLike
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra

/-!
# The bialgebra structure on monoid algebras

Given a monoid `M`, a commutative semiring `R` and an `R`-bialgebra `A`, this file collects results
about the `R`-bialgebra instance on `A[M]` inherited from the corresponding structure on its
coefficients, building upon results in `Mathlib/RingTheory/Coalgebra/MonoidAlgebra.lean` about the
coalgebra structure.

## Main definitions

* `(Add)MonoidAlgebra.instBialgebra`: the `R`-bialgebra structure on `A[M]` when `M` is an (add)
  monoid and `A` is an `R`-bialgebra.
* `LaurentPolynomial.instBialgebra`: the `R`-bialgebra structure on the Laurent polynomials
  `A[T;T⁻¹]` when `A` is an `R`-bialgebra.
* `(Add)MonoidAlgebra.mapDomainBialgHomEquiv`: isomorphism between `R`-bialgebra homs `A[G] → A[H]`
  and groups homs `G → H` when `G` and `H` are an (add) group and `A` is an `R`-bialgebra.
-/

public noncomputable section

open TensorProduct Bialgebra Coalgebra Function WithConv

variable {R S A B G H I M N O : Type*}

namespace MonoidAlgebra
section CommSemiring
variable [CommSemiring R] [CommSemiring S]

section Semiring
variable [Semiring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]

@[to_additive (dont_translate := R A) (attr := simp) isGroupLikeElem_single_one]
/-
**MonoidAlgebra.isGroupLikeElem_single_one** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlge
bra`。
形式化陈述：isGroupLikeElem_single_one (g : G) : IsGroupLikeElem R (single g 1 : A[G])
 where counit_eq_one
参数：g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.counit_single`：counit_single (x : X) (a : A) : Coalgebra.c
ounit (single x a) = Coalgebra.counit (R
· 使用定理 `Bialgebra.counit_one`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R
} {inst_1 : Semiring A} [self : Bialgebra R A],   CoalgebraStruct.counit 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MonoidAlgebra.comul_single`：comul_single (x : X) (a : A) : Coalgebra.com
ul (R
· 使用定理 `Bialgebra.comul_one`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R}
 {inst_1 : Semiring A} [self : Bialgebra R A],   CoalgebraStruct.comul 1 = 1
-/
lemma isGroupLikeElem_single_one (g : G) : IsGroupLikeElem R (single g 1 : A[G]) where
  counit_eq_one := by simp
  comul_eq_tmul_self := by simp [Algebra.TensorProduct.one_def]

/-- A group algebra is spanned by its group-like elements. -/
@[to_additive (dont_translate := R A) (attr := simp) span_isGroupLikeElem]
/-
**MonoidAlgebra.span_isGroupLikeElem** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：span_isGroupLikeElem : Submodule.span A {a : A[G] | IsGroupLikeElem R a} =
 ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_mono`：eq_top_mono (h : a <= b) (h₂ : a = ⊤) : b = ⊤
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用引理 `MonoidAlgebra.isGroupLikeElem_single_one`：isGroupLikeElem_single_one (g 
: G) : IsGroupLikeElem R (single g 1 : A[G]) where counit_eq_one
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.range_linearCombination`：range_linearCombination : LinearMap.ran
ge (linearCombination R v) = span R (range v)
· 使用定理 `LinearMap.range_eq_top_of_surjective`：range_eq_top_of_surjective [RingHo
mSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (hf : Surjective f) : range f = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MonoidAlgebra.smul_single`：smul_single (a : A) (m : M) (r : R) : a • sin
gle m r = single m (a • r)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `MonoidAlgebra.sum_coeff_single`：sum_coeff_single (f : R[M]) : f.coeff.su
m single = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A group algebra is spanned by its group-like elements.
-/
lemma span_isGroupLikeElem : Submodule.span A {a : A[G] | IsGroupLikeElem R a} = ⊤ :=
  eq_top_mono (Submodule.span_mono <| Set.range_subset_iff.2 isGroupLikeElem_single_one) <| by
    rw [← Finsupp.range_linearCombination]
    exact LinearMap.range_eq_top_of_surjective _ fun x ↦
      ⟨x.coeff, by simp [Finsupp.linearCombination_apply]⟩

variable [Monoid M] [Monoid N] [Monoid O]

variable (R A M) in
@[to_additive (dont_translate := R A)]
/-
**MonoidAlgebra.instBialgebra** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
形式化陈述：instBialgebra : Bialgebra R A[M] where counit_one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBialgebra : Bialgebra R A[M] where
  counit_one := by simp only [one_def, counit_single, Bialgebra.counit_one]
  mul_compr₂_counit := by ext; simp
  comul_one := by
    simp only [one_def, comul_single, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
      TensorProduct.map_tmul, lsingle_apply]
  mul_compr₂_comul := by
    ext a b c d
    simp only [Function.comp_apply, LinearMap.coe_comp, LinearMap.compr₂_apply,
      LinearMap.mul_apply', single_mul_single, comul_single, Bialgebra.comul_mul,
      ← (Coalgebra.Repr.arbitrary R b).eq, ← (Coalgebra.Repr.arbitrary R d).eq, Finset.sum_mul_sum,
      Algebra.TensorProduct.tmul_mul_tmul, map_sum, TensorProduct.map_tmul, lsingle_apply,
      LinearMap.compl₁₂_apply, LinearMap.coe_sum, Finset.sum_apply,
      Finset.sum_comm (s := (Coalgebra.Repr.arbitrary R b).index)]

-- TODO: Generalise to `A[M] →ₐc[R] A[N]` under `Bialgebra R A`
variable (R) in
/-- If `f : M → N` is a monoid hom, then `MonoidAlgebra.mapDomain f` is a bialgebra hom between
their monoid algebras. -/
@[expose, to_additive (attr := simps!) (dont_translate := R)
/-- If `f : M → N` is an additive monoid hom, then `MonoidAlgebra.mapDomain f` is a bialgebra hom
between their additive monoid algebras. -/]
/-
**MonoidAlgebra.mapDomainBialgHom** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomainBialgHom (f : M ->* N) : R[M] ->ₐc[R] R[N]
参数：f : M ->* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapDomainBialgHom (f : M →* N) : R[M] →ₐc[R] R[N] :=
  .ofAlgHom (mapDomainAlgHom R R f) (by ext; simp) (by ext; simp)

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapDomainBialgHom_id** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomainBialgHom_id : mapDomainBialgHom R (.id M) = .id R R[M]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHom.ext`：ext {φ₁ φ₂ : A ->ₐc[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁
 = φ₂
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidAlgebra.coeff_mapDomainBialgHom_apply`：∀ (R : Type u_1) {M : Type 
u_8} {N : Type u_9} [inst : CommSemiring R] [inst_1 : Monoid M] [inst_2 : Monoid
 N]   (f : M →* N) (a : MonoidAlg…
· 使用定理 `Finsupp.mapDomain_id`：mapDomain_id : mapDomain id v = v
· 使用定理 `BialgHom.id_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : CoalgebraStruct R A]
 (x : A…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainBialgHom_id : mapDomainBialgHom R (.id M) = .id R R[M] := by ext; simp

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapDomainBialgHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`
。
形式化陈述：mapDomainBialgHom_comp (f : N ->* O) (g : M ->* N) : mapDomainBialgHom R (
f.comp g) = (mapDomainBialgHom R f).comp (mapDomainBialgHom R g)
参数：f : N ->* O；g : M ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHom.ext`：ext {φ₁ φ₂ : A ->ₐc[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁
 = φ₂
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidAlgebra.coeff_mapDomainBialgHom_apply`：∀ (R : Type u_1) {M : Type 
u_8} {N : Type u_9} [inst : CommSemiring R] [inst_1 : Monoid M] [inst_2 : Monoid
 N]   (f : M →* N) (a : MonoidAlg…
· 使用定理 `Finsupp.mapDomain_comp`：mapDomain_comp {f : α -> β} {g : β -> γ} : mapDo
main (g ∘ f) v = mapDomain g (mapDomain f v)
· 使用定理 `BialgHom.comp_apply`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} {C :
 Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Semiring B]
 [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainBialgHom_comp (f : N →* O) (g : M →* N) :
    mapDomainBialgHom R (f.comp g) = (mapDomainBialgHom R f).comp (mapDomainBialgHom R g) := by
  ext; simp [Finsupp.mapDomain_comp]

@[to_additive]
/-
**MonoidAlgebra.mapDomainBialgHom_mapDomainBialgHom** 是 Mathlib 中的一个引理，位于命名空间 `M
onoidAlgebra`。
形式化陈述：mapDomainBialgHom_mapDomainBialgHom (f : N ->* O) (g : M ->* N) (x : R[M])
 : mapDomainBialgHom R f (mapDomainBialgHom R g x) = mapDomainBialgHom R (f.comp
 g) x
参数：f : N ->* O；g : M ->* N；x : R[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidAlgebra.coeff_mapDomainBialgHom_apply`：∀ (R : Type u_1) {M : Type 
u_8} {N : Type u_9} [inst : CommSemiring R] [inst_1 : Monoid M] [inst_2 : Monoid
 N]   (f : M →* N) (a : MonoidAlg…
· 使用引理 `MonoidAlgebra.mapDomainBialgHom_comp`：mapDomainBialgHom_comp (f : N ->* 
O) (g : M ->* N) : mapDomainBialgHom R (f.comp g) = (mapDomainBialgHom R f).comp
 (mapDomainBialgHom R g)
· 使用定理 `BialgHom.comp_apply`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} {C :
 Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Semiring B]
 [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainBialgHom_mapDomainBialgHom (f : N →* O) (g : M →* N) (x : R[M]) :
    mapDomainBialgHom R f (mapDomainBialgHom R g x) = mapDomainBialgHom R (f.comp g) x := by
  ext; simp

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapDomainBialgHom_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebr
a`。
形式化陈述：mapDomainBialgHom_single (f : M ->* N) (m : M) (r : R) : mapDomainBialgHom
 R f (single m r) = single (f m) r
参数：f : M ->* N；m : M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.mapDomain_single`：mapDomain_single : mapDomain f (single a
 r) = single (f a) r
-/
lemma mapDomainBialgHom_single (f : M →* N) (m : M) (r : R) :
    mapDomainBialgHom R f (single m r) = single (f m) r := mapDomain_single

/-- A `R`-bialgebra homomorphism from `A[M]` is uniquely defined by its
values on the functions `single m 1` and `single 1 a`.

See note [partially-applied ext lemmas]. Note that the first assumption isn't written as an
equality of `MonoidHom`s because `of` doesn't additivise. -/
@[to_additive (dont_translate := A) (attr := ext high)
/-- A `R`-bialgebra homomorphism from `A[M]` is uniquely defined by its
values on the functions `single m 1` and `single 1 a`.

See note [partially-applied ext lemmas]. Note that the first assumption isn't written as an
equality of `AddMonoidHom`s because `of` doesn't multiplicativise. -/]
/-
**MonoidAlgebra.bialgHom_ext** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：bialgHom_ext ⦃φ₁ φ₂ : A[M] ->ₐc[R] B⦄ (single_one_right : forall (m : M), 
φ₁ (single m 1) = φ₂ (single m 1)) (single_one_left : (φ₁ : A[M] ->ₐ[R] B).comp 
singleOneAlgHom = (φ₂ : A[M] ->ₐ[R] B).comp singleOneAlgHom) : φ₁ = φ₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHom.coe_toAlgHom_injective`：coe_toAlgHom_injective : Function.Injec
tive ((↑) : (A ->ₐc[R] B) -> A ->ₐ[R] B)
· 使用引理 `MonoidAlgebra.algHom_ext`：algHom_ext ⦃φ₁ φ₂ : A[M] ->ₐ[R] B⦄ (single_one
_right : forall m, φ₁ (single m 1) = φ₂ (single m 1)) (single_one_left : φ₁.comp
 singleOneAlgH…
-/
lemma bialgHom_ext ⦃φ₁ φ₂ : A[M] →ₐc[R] B⦄
  (single_one_right : ∀ (m : M), φ₁ (single m 1) = φ₂ (single m 1))
  (single_one_left : (φ₁ : A[M] →ₐ[R] B).comp singleOneAlgHom =
    (φ₂ : A[M] →ₐ[R] B).comp singleOneAlgHom) : φ₁ = φ₂ :=
  BialgHom.coe_toAlgHom_injective <| algHom_ext single_one_right single_one_left

/-- Version of `bialgHom_ext` where both assumptions are written as equalities of bundled homs. -/
/-
**MonoidAlgebra.bialgHom_ext'** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：bialgHom_ext' ⦃φ₁ φ₂ : A[M] ->ₐc[R] B⦄ (single_one_right : (φ₁ : A[M] ->* 
B).comp (of A M) = (φ₂ : A[M] ->* B).comp (of A M)) (single_one_left : (φ₁ : A[M
] ->ₐ[R] B).comp singleOneAlgHom = (φ₂ : A[M] ->ₐ[R] B).comp singleOneAlgHom) : 
φ₁ = φ₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHomClass.toMonoidHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `BialgHom.coe_toAlgHom_injective`：coe_toAlgHom_injective : Function.Injec
tive ((↑) : (A ->ₐc[R] B) -> A ->ₐ[R] B)
· 使用引理 `MonoidAlgebra.algHom_ext'`：algHom_ext' ⦃φ₁ φ₂ : A[M] ->ₐ[R] B⦄ (single_o
ne_right : (φ₁ : A[M] ->* B).comp (of A M) = (φ₂ : A[M] ->* B).comp (of A M)) (s
ingle_one_left …

--- 原说明 ---
Version of `bialgHom_ext` where both assumptions are written as equalities of bu
ndled homs.
-/
lemma bialgHom_ext' ⦃φ₁ φ₂ : A[M] →ₐc[R] B⦄
    (single_one_right : (φ₁ : A[M] →* B).comp (of A M) = (φ₂ : A[M] →* B).comp (of A M))
    (single_one_left : (φ₁ : A[M] →ₐ[R] B).comp singleOneAlgHom =
      (φ₂ : A[M] →ₐ[R] B).comp singleOneAlgHom) : φ₁ = φ₂ :=
  BialgHom.coe_toAlgHom_injective <| algHom_ext' single_one_right single_one_left

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.counit_domCongr** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：counit_domCongr (e : M ≃* N) (x : A[M]) : counit (R
参数：e : M ≃* N；x : A[M]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.induction_linear`：induction_linear {motive : R[M] -> Prop}
 (x : R[M]) (zero : motive 0) (add : forall x y : R[M], motive x -> motive y -> 
motive (x + y)) (sin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
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
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MonoidAlgebra.domCongr_single`：domCongr_single (e : M ≃* N) (m : M) (a :
 A) : domCongr R A e (single m a) = single (e m) a
· 使用引理 `MonoidAlgebra.counit_single`：counit_single (x : X) (a : A) : Coalgebra.c
ounit (single x a) = Coalgebra.counit (R
-/
lemma counit_domCongr (e : M ≃* N) (x : A[M]) : counit (R := R) (domCongr R A e x) = counit x := by
  induction x using MonoidAlgebra.induction_linear <;> simp [*]

variable (R A) in
-- TODO: Make `BialgEquiv.toCoalgEquiv` the simp normal form so that this can be simp
/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[expose, to_additive (attr := simps! -isSimp) (dont_translate := R A)
/-- Isomorphic monoids have isomorphic monoid algebras. -/]
/-
**MonoidAlgebra.domCongrBialgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：domCongrBialgEquiv (e : M ≃* N) : A[M] ≃ₐc[R] A[N]
参数：e : M ≃* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def domCongrBialgEquiv (e : M ≃* N) : A[M] ≃ₐc[R] A[N] :=
  .ofAlgEquiv (domCongr R A e) (by ext <;> simp) <| by
    ext a
    · simp
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

variable (M) in
/-- The trivial monoid algebra is isomorphic to the base ring. -/
@[expose, to_additive (dont_translate := R)
/-- The trivial monoid algebra is isomorphic to the base ring. -/]
/-
**MonoidAlgebra.bialgEquivOfSubsingleton** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebr
a`。
形式化陈述：bialgEquivOfSubsingleton [Subsingleton M] : R[M] ≃ₐc[R] R where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def bialgEquivOfSubsingleton [Subsingleton M] : R[M] ≃ₐc[R] R where
  __ := counitBialgHom ..
  invFun := algebraMap _ _
  left_inv r := by
    change (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R _) r = AlgHom.id R _ r
    congr 1
    ext g : 2
    simp [Subsingleton.elim g 1]
  right_inv := (Bialgebra.counitAlgHom R R[M]).commutes
/-
**MonoidAlgebra.isGroupLikeElem_of** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：isGroupLikeElem_of (m : M) : IsGroupLikeElem R (of A M m)
参数：m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.isGroupLikeElem_single_one`：isGroupLikeElem_single_one (g 
: G) : IsGroupLikeElem R (single g 1 : A[G]) where counit_eq_one
-/
lemma isGroupLikeElem_of (m : M) : IsGroupLikeElem R (of A M m) := isGroupLikeElem_single_one ..

/-- The `R`-bialgebra map from the group algebra on the group-like elements of `A` to `A`. -/
@[expose, simps!]
/-
**MonoidAlgebra.liftGroupLikeBialgHom** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：liftGroupLikeBialgHom : R[GroupLike R A] ->ₐc[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-bialgebra map from the group algebra on the group-like elements of `A` t
o `A`.
-/
def liftGroupLikeBialgHom : R[GroupLike R A] →ₐc[R] A :=
  .ofAlgHom (lift R A (GroupLike R A) { toFun g := g.1, map_one' := by simp, map_mul' := by simp })
    (by ext; simp) (by ext; simp)

variable (R A M) in
/-- The bialgebra equivalence between `MonoidAlgebra` and `AddMonoidAlgebra` in terms of
`Additive`. -/
-- TODO: Make `BialgEquiv.toCoalgEquiv` the simp normal form so that this can be simp
@[expose, simps! -isSimp]
/-
**MonoidAlgebra.toAdditiveBialgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：toAdditiveBialgEquiv : A[M] ≃ₐc[R] AddMonoidAlgebra A (Additive M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toAdditiveBialgEquiv : A[M] ≃ₐc[R] AddMonoidAlgebra A (Additive M) :=
  .ofAlgEquiv (toAdditiveAlgEquiv R A M) (by ext <;> simp) <| by
    ext a
    · simp
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

@[simp]
/-
**MonoidAlgebra.toAdditiveBialgEquiv_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlg
ebra`。
形式化陈述：toAdditiveBialgEquiv_single (m : M) (a : A) : toAdditiveBialgEquiv R A M (
single m a) = .single (.ofMul m) a
参数：m : M；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BialgEquiv.ofAlgEquiv_apply`：∀ {R : Type u} {A : Type v} {B : Type w} [i
nst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Bi
algebra R A] [ins…
· 使用引理 `MonoidAlgebra.toAdditiveAlgEquiv_single`：toAdditiveAlgEquiv_single (m : 
M) (a : A) : toAdditiveAlgEquiv R A M (single m a) = .single (.ofMul m) a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toAdditiveBialgEquiv_single (m : M) (a : A) :
    toAdditiveBialgEquiv R A M (single m a) = .single (.ofMul m) a := by
  simp [toAdditiveBialgEquiv]

end Semiring

section CommSemiring
variable [CommSemiring A]

section Algebra
variable [Algebra R A] [Monoid M]

variable (R M A) in
/-- `MonoidAlgebra.lift` as a `MulEquiv`. -/
/-
**MonoidAlgebra.liftMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：liftMulEquiv : (M ->* A) ≃* WithConv (R[M] ->ₐ[R] A) where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`MonoidAlgebra.lift` as a `MulEquiv`.
-/
def liftMulEquiv : (M →* A) ≃* WithConv (R[M] →ₐ[R] A) where
  toEquiv := (lift R A M).trans (WithConv.equiv _).symm
  map_mul' f g := by ext; simp [AlgHom.convMul_apply]

@[to_additive (dont_translate := R A) (attr := simp) convMul_algHom_single_one]
/-
**MonoidAlgebra.convMul_algHom_single_one** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgeb
ra`。
形式化陈述：convMul_algHom_single_one (f g : WithConv <| R[M] ->ₐ[R] A) (x : M) : (f *
 g) (single x 1) = f (single x 1) * g (single x 1)
参数：f g : WithConv <| R[M] ->ₐ[R] A；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用引理 `AlgHom.convMul_apply`：convMul_apply (f g : WithConv <| C ->ₐ[R] A) (c : 
C) : (f * g) c = lift f.ofConv g.ofConv (fun _ _ => .all ..) (comul c)
· 使用定理 `IsGroupLikeElem.comul_eq_tmul_self`：∀ {R : Type u_2} {A : Type u_3} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [i
nst_3 : Coalgebra R A] {…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma convMul_algHom_single_one (f g : WithConv <| R[M] →ₐ[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by simp [AlgHom.convMul_apply]

end Algebra

variable [Bialgebra R A]

@[to_additive (dont_translate := R A) (attr := simp) convMul_bialgHom_single_one]
/-
**MonoidAlgebra.convMul_bialgHom_single_one** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlg
ebra`。
形式化陈述：convMul_bialgHom_single_one [CommMonoid M] (f g : WithConv <| R[M] ->ₐc[R]
 A) (x : M) : (f * g) (single x 1) = f (single x 1) * g (single x 1)
参数：f g : WithConv <| R[M] ->ₐc[R] A；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommSemiring.instIsCocomm`：∀ (R : Type u) [inst : CommSemiring R], Coalg
ebra.IsCocomm R R
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsGroupLikeElem.comul_eq_tmul_self`：∀ {R : Type u_2} {A : Type u_3} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [i
nst_3 : Coalgebra R A] {…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma convMul_bialgHom_single_one [CommMonoid M] (f g : WithConv <| R[M] →ₐc[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by
  simp only [BialgHom.convMul_def, BialgHom.coe_comp, Function.comp_apply]
  change mulBialgHom R A (Bialgebra.TensorProduct.map f.ofConv g.ofConv (comul (single x 1))) = _
  simp [Bialgebra.TensorProduct.map_tmul]

end CommSemiring

section CommMonoid
variable [CommMonoid M] [CommMonoid N]

@[to_additive (dont_translate := R) (attr := simp)]
/-
**MonoidAlgebra.mapDomainBialgHom_mul** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomainBialgHom_mul (f g : M ->* N) : mapDomainBialgHom R (f * g) = ofCo
nv ((toConv <| mapDomainBialgHom R f) * (toConv <| mapDomainBialgHom R g))
参数：f g : M ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.bialgHom_ext`：bialgHom_ext ⦃φ₁ φ₂ : A[M] ->ₐc[R] B⦄ (singl
e_one_right : forall (m : M), φ₁ (single m 1) = φ₂ (single m 1)) (single_one_lef
t : (φ₁ : A[M] -…
· 使用定理 `CommSemiring.instIsCocomm`：∀ (R : Type u) [inst : CommSemiring R], Coalg
ebra.IsCocomm R R
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MonoidAlgebra.mapDomainBialgHom_single`：mapDomainBialgHom_single (f : M 
->* N) (m : M) (r : R) : mapDomainBialgHom R f (single m r) = single (f m) r
· 使用引理 `MonoidAlgebra.convMul_bialgHom_single_one`：convMul_bialgHom_single_one [
CommMonoid M] (f g : WithConv <| R[M] ->ₐc[R] A) (x : M) : (f * g) (single x 1) 
= f (single x 1) * g (single x …
· 使用引理 `MonoidAlgebra.single_mul_single`：single_mul_single (m₁ m₂ : M) (r₁ r₂ : 
R) : single m₁ r₁ * single m₂ r₂ = single (m₁ * m₂) (r₁ * r₂)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.ext_id`：ext_id (f g : R ->ₐ[R] A) : f = g
-/
lemma mapDomainBialgHom_mul (f g : M →* N) :
    mapDomainBialgHom R (f * g) =
      ofConv ((toConv <| mapDomainBialgHom R f) * (toConv <| mapDomainBialgHom R g)) := by ext; simp
/-
**MonoidAlgebra.comulAlgHom_comp_mapRingHom** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlg
ebra`。
形式化陈述：comulAlgHom_comp_mapRingHom (f : R ->+* S) : (comulAlgHom S (MonoidAlgebra
 S M)).toRingHom.comp (mapRingHom M f) = .comp (Algebra.TensorProduct.mapRingHom
 f (mapRingHom M f) (mapRingHom M f) (by simp) (by simp)) (comulAlgHom R R[M]).t
oRingHom
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.ringHom_ext'`：ringHom_ext' [Semiring S] {f g : R[M] ->+* S
} (h₁ : f.comp singleOneRingHom = g.comp singleOneRingHom) (h_of : (f : R[M] ->*
 S).comp (of R M…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.singleOneRingHom_apply`：∀ {R : Type u_1} {M : Type u_4} [i
nst : Semiring R] [inst_1 : MulOneClass M] (a : R),   MonoidAlgebra.singleOneRin
gHom a = (↑(MonoidAlgebra.…
· 使用定理 `MonoidAlgebra.singleAddHom_apply`：∀ {R : Type u_1} {M : Type u_4} [inst 
: Semiring R] (m : M) (r : R),   (MonoidAlgebra.singleAddHom m) r = MonoidAlgebr
a.single m r
· 使用引理 `MonoidAlgebra.mapRingHom_single`：mapRingHom_single (f : R ->+* S) (a : M
) (b : R) : mapRingHom M f (single a b) = single a (f b)
· 使用定理 `Bialgebra.comulAlgHom_apply`：∀ (R : Type u) (A : Type v) [inst : CommSem
iring R] [inst_1 : Semiring A] [inst_2 : Bialgebra R A] (a : A),   (Bialgebra.co
mulAlgHom R A) a …
· 使用引理 `MonoidAlgebra.comul_single`：comul_single (x : X) (a : A) : Coalgebra.com
ul (R
· 使用引理 `Algebra.TensorProduct.mapRingHom_tmul`：mapRingHom_tmul (s : S) (t : T) :
 mapRingHom fR fS fT HS HT (s otimesₜ t) = fS s otimesₜ fT t
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用定理 `IsGroupLikeElem.comul_eq_tmul_self`：∀ {R : Type u_2} {A : Type u_3} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [i
nst_3 : Coalgebra R A] {…
-/
lemma comulAlgHom_comp_mapRingHom (f : R →+* S) :
    (comulAlgHom S (MonoidAlgebra S M)).toRingHom.comp (mapRingHom M f) =
      .comp (Algebra.TensorProduct.mapRingHom f (mapRingHom M f) (mapRingHom M f) (by simp)
        (by simp)) (comulAlgHom R R[M]).toRingHom := by ext <;> simp
/-
**MonoidAlgebra.counitAlgHom_comp_mapRingHom** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAl
gebra`。
形式化陈述：counitAlgHom_comp_mapRingHom (f : R ->+* S) : (counitAlgHom S (MonoidAlgeb
ra S M)).toRingHom.comp (mapRingHom M f) = f.comp (counitAlgHom R R[M]).toRingHo
m
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.ringHom_ext'`：ringHom_ext' [Semiring S] {f g : R[M] ->+* S
} (h₁ : f.comp singleOneRingHom = g.comp singleOneRingHom) (h_of : (f : R[M] ->*
 S).comp (of R M…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.singleOneRingHom_apply`：∀ {R : Type u_1} {M : Type u_4} [i
nst : Semiring R] [inst_1 : MulOneClass M] (a : R),   MonoidAlgebra.singleOneRin
gHom a = (↑(MonoidAlgebra.…
· 使用定理 `MonoidAlgebra.singleAddHom_apply`：∀ {R : Type u_1} {M : Type u_4} [inst 
: Semiring R] (m : M) (r : R),   (MonoidAlgebra.singleAddHom m) r = MonoidAlgebr
a.single m r
· 使用引理 `MonoidAlgebra.mapRingHom_single`：mapRingHom_single (f : R ->+* S) (a : M
) (b : R) : mapRingHom M f (single a b) = single a (f b)
· 使用定理 `Bialgebra.counitAlgHom_apply`：∀ (R : Type u) (A : Type v) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Bialgebra R A] (a : A),   (Bialgebra.c
ounitAlgHom R A) a…
· 使用引理 `MonoidAlgebra.counit_single`：counit_single (x : X) (a : A) : Coalgebra.c
ounit (single x a) = Coalgebra.counit (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `IsGroupLikeElem.counit_eq_one`：∀ {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3
 : Coalgebra R A] {…
-/
lemma counitAlgHom_comp_mapRingHom (f : R →+* S) :
    (counitAlgHom S (MonoidAlgebra S M)).toRingHom.comp (mapRingHom M f) =
      f.comp (counitAlgHom R R[M]).toRingHom := by ext <;> simp

end CommMonoid
end CommSemiring

section CommRing
variable [CommRing R] [IsDomain R]

open Submodule in
@[to_additive (dont_translate := R) isGroupLikeElem_iff_mem_range_single_one]
/-
**MonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one** 是 Mathlib 中的一个引理，位于命名
空间 `MonoidAlgebra`。
形式化陈述：isGroupLikeElem_iff_mem_range_single_one {x : R[M]} : IsGroupLikeElem R x 
↔ x in Set.range (single · 1) where mp hx
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `LinearIndepOn.mono`：LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn
 R v s) (h : t subseteq s) : LinearIndepOn R v t
· 使用引理 `linearIndepOn_isGroupLikeElem`：linearIndepOn_isGroupLikeElem : LinearInd
epOn R id {a : A | IsGroupLikeElem R a}
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `MonoidAlgebra.sum_coeff_single`：sum_coeff_single (f : R[M]) : f.coeff.su
m single = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用引理 `LinearIndepOn.notMem_span_of_insert`：LinearIndepOn.notMem_span_of_insert
 (hv : LinearIndepOn R v (insert i s)) (hi : i ∉ s) : v i ∉ span R (v '' s)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `MonoidAlgebra.smul_single`：smul_single (a : A) (m : M) (r : R) : a • sin
gle m r = single m (a • r)
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用引理 `MonoidAlgebra.isGroupLikeElem_single_one`：isGroupLikeElem_single_one (g 
: G) : IsGroupLikeElem R (single g 1 : A[G]) where counit_eq_one
-/
lemma isGroupLikeElem_iff_mem_range_single_one {x : R[M]} :
    IsGroupLikeElem R x ↔ x ∈ Set.range (single · 1) where
  mp hx := by
    by_contra h
    have : LinearIndepOn R id (insert x <| .range (single · 1)) :=
      linearIndepOn_isGroupLikeElem.mono <| by simp [Set.subset_def, hx]
    have : x.coeff.sum single ∉ span R (.range (single · 1)) := by
      simpa using this.notMem_span_of_insert h
    refine this <| sum_mem fun g hg ↦ ?_
    rw [← mul_one (x.coeff g), ← smul_eq_mul, ← smul_single]
    exact smul_mem _ _ <| subset_span <| Set.mem_range_self _
  mpr := by rintro ⟨g, rfl⟩; exact isGroupLikeElem_single_one _

section MulOneClass
variable [MulOneClass M] {x : R[M]}

/-
**MonoidAlgebra.isGroupLikeElem_iff_mem_range_of** 是 Mathlib 中的一个引理，位于命名空间 `Mono
idAlgebra`。
形式化陈述：isGroupLikeElem_iff_mem_range_of : IsGroupLikeElem R x ↔ x in Set.range (o
f R M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one`：isGroupLikeElem_
iff_mem_range_single_one {x : R[M]} : IsGroupLikeElem R x ↔ x in Set.range (sing
le · 1) where mp hx
-/
lemma isGroupLikeElem_iff_mem_range_of : IsGroupLikeElem R x ↔ x ∈ Set.range (of R M) :=
  isGroupLikeElem_iff_mem_range_single_one

end MulOneClass

section Group
variable [Group G] [Group H] [Group I]

@[to_additive (dont_translate := R)]
/-
**MonoidAlgebra.mapDomainOfBialgHomFun** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def mapDomainOfBialgHomFun (f : R[G] →ₐc[R] R[H]) (g : G) : H :=
  (isGroupLikeElem_iff_mem_range_single_one.1 <| (isGroupLikeElem_single_one g).map f).choose

@[to_additive (dont_translate := R) (attr := simp)]
/-
**MonoidAlgebra.single_mapDomainOfBialgHomFun_one** 是 Mathlib 中的一个引理，位于命名空间 `Mon
oidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma single_mapDomainOfBialgHomFun_one (f : R[G] →ₐc[R] R[H]) (g : G) :
    single (mapDomainOfBialgHomFun f g) 1 = f (single g 1) :=
  (isGroupLikeElem_iff_mem_range_single_one.1 <| (isGroupLikeElem_single_one g).map f).choose_spec

/-- A bialgebra homomorphism `R[G] → R[H]` between group algebras over a domain `R` comes from a
group hom `G → H`.

See `MonoidAlgebra.mapDomainBialgHom` for the forward map. -/
@[to_additive (dont_translate := R)
/-- A bialgebra homomorphism `R[G] → R[H]` between group algebras over a domain `R` comes from a
group hom `G → H`.

See `MonoidAlgebra.mapDomainBialgHom` for the forward map. -/]
/-
**MonoidAlgebra.mapDomainOfBialgHom** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomainOfBialgHom (f : R[G] ->ₐc[R] R[H]) : G ->* H where toFun
参数：f : R[G] ->ₐc[R] R[H]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapDomainOfBialgHom (f : R[G] →ₐc[R] R[H]) : G →* H where
  toFun := mapDomainOfBialgHomFun f
  map_one' := single_left_injective (R := R) one_ne_zero <| by simp [← one_def]
  map_mul' g₁ g₂ := by
    refine single_left_injective (R := R) one_ne_zero ?_
    simp only [single_mapDomainOfBialgHomFun_one]
    rw [← mul_one (1 : R), ← single_mul_single, ← single_mul_single, map_mul]
    simp

@[to_additive (dont_translate := R) (attr := simp)]
/-
**MonoidAlgebra.single_mapDomainOfBialgHom** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlge
bra`。
形式化陈述：single_mapDomainOfBialgHom (f : R[G] ->ₐc[R] R[H]) (g : G) (r : R) : singl
e (mapDomainOfBialgHom f g) r = f (single g r)
参数：f : R[G] ->ₐc[R] R[H]；g : G；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `MonoidAlgebra.smul_single`：smul_single (a : A) (m : M) (r : R) : a • sin
gle m r = single m (a • r)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
· 使用定理 `BialgHomClass.toCoalgHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)
} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   
{inst_1 : Semiring …
· 使用定理 `_private.Mathlib.RingTheory.Bialgebra.MonoidAlgebra.0.MonoidAlgebra.sing
le_mapDomainOfBialgHomFun_one`：∀ {R : Type u_1} {G : Type u_5} {H : Type u_6} [i
nst : CommRing R] [inst_1 : IsDomain R] [inst_2 : Group G]   [inst_3 : Group H] 
(f : Monoid…
-/
lemma single_mapDomainOfBialgHom (f : R[G] →ₐc[R] R[H]) (g : G) (r : R) :
    single (mapDomainOfBialgHom f g) r = f (single g r) := by
  rw [← mul_one r, ← smul_eq_mul, ← smul_single, ← smul_single, map_smul]
  exact congr(r • $(single_mapDomainOfBialgHomFun_one f g))

@[to_additive (dont_translate := R) (attr := simp)]
/-
**MonoidAlgebra.mapDomainBialgHom_mapDomainOfBialgHom** 是 Mathlib 中的一个引理，位于命名空间 
`MonoidAlgebra`。
形式化陈述：mapDomainBialgHom_mapDomainOfBialgHom (f : R[G] ->ₐc[R] R[H]) : mapDomainB
ialgHom R (mapDomainOfBialgHom f) = f
参数：f : R[G] ->ₐc[R] R[H]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.bialgHom_ext`：bialgHom_ext ⦃φ₁ φ₂ : A[M] ->ₐc[R] B⦄ (singl
e_one_right : forall (m : M), φ₁ (single m 1) = φ₂ (single m 1)) (single_one_lef
t : (φ₁ : A[M] -…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.mapDomainBialgHom_single`：mapDomainBialgHom_single (f : M 
->* N) (m : M) (r : R) : mapDomainBialgHom R f (single m r) = single (f m) r
· 使用定理 `_private.Mathlib.RingTheory.Bialgebra.MonoidAlgebra.0.MonoidAlgebra.sing
le_mapDomainOfBialgHomFun_one`：∀ {R : Type u_1} {G : Type u_5} {H : Type u_6} [i
nst : CommRing R] [inst_1 : IsDomain R] [inst_2 : Group G]   [inst_3 : Group H] 
(f : Monoid…
· 使用定理 `Algebra.ext_id`：ext_id (f g : R ->ₐ[R] A) : f = g
-/
lemma mapDomainBialgHom_mapDomainOfBialgHom (f : R[G] →ₐc[R] R[H]) :
    mapDomainBialgHom R (mapDomainOfBialgHom f) = f := by
  ext x : 1
  · rw [mapDomainBialgHom_single]
    exact single_mapDomainOfBialgHomFun_one f x
  · ext

@[to_additive (dont_translate := R) (attr := simp)]
/-
**MonoidAlgebra.mapDomainOfBialgHom_mapDomainBialgHom** 是 Mathlib 中的一个引理，位于命名空间 
`MonoidAlgebra`。
形式化陈述：mapDomainOfBialgHom_mapDomainBialgHom (f : G ->* H) : mapDomainOfBialgHom 
(mapDomainBialgHom (R
参数：f : G ->* H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用引理 `MonoidAlgebra.single_left_injective`：single_left_injective (hr : r != 0)
 : Function.Injective fun m : M => single m r
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.single_mapDomainOfBialgHom`：single_mapDomainOfBialgHom (f 
: R[G] ->ₐc[R] R[H]) (g : G) (r : R) : single (mapDomainOfBialgHom f g) r = f (s
ingle g r)
· 使用引理 `MonoidAlgebra.mapDomainBialgHom_single`：mapDomainBialgHom_single (f : M 
->* N) (m : M) (r : R) : mapDomainBialgHom R f (single m r) = single (f m) r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainOfBialgHom_mapDomainBialgHom (f : G →* H) :
    mapDomainOfBialgHom (mapDomainBialgHom (R := R) f) = f := by
  ext g; refine single_left_injective (R := R) one_ne_zero ?_; simp [single_mapDomainOfBialgHom]

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapDomainOfBialgHom_id** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`
。
形式化陈述：mapDomainOfBialgHom_id : mapDomainOfBialgHom (.id R R[G]) = .id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.mapDomainOfBialgHom.congr_simp`：∀ {R : Type u_1} {G : Type
 u_5} {H : Type u_6} [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : Group G
]   [inst_3 : Group H] (f f_1 : Mo…
· 使用引理 `MonoidAlgebra.mapDomainOfBialgHom_mapDomainBialgHom`：mapDomainOfBialgHom
_mapDomainBialgHom (f : G ->* H) : mapDomainOfBialgHom (mapDomainBialgHom (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainOfBialgHom_id : mapDomainOfBialgHom (.id R R[G]) = .id _ := by
  simp [← mapDomainBialgHom_id]

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapDomainOfBialgHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebr
a`。
形式化陈述：mapDomainOfBialgHom_comp (f : R[H] ->ₐc[R] R[I]) (g : R[G] ->ₐc[R] R[H]) :
 mapDomainOfBialgHom (f.comp g) = (mapDomainOfBialgHom f).comp (mapDomainOfBialg
Hom g)
参数：f : R[H] ->ₐc[R] R[I]；g : R[G] ->ₐc[R] R[H]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MonoidAlgebra.mapDomainOfBialgHom_mapDomainBialgHom`：mapDomainOfBialgHom
_mapDomainBialgHom (f : G ->* H) : mapDomainOfBialgHom (mapDomainBialgHom (R
· 使用引理 `MonoidAlgebra.mapDomainBialgHom_comp`：mapDomainBialgHom_comp (f : N ->* 
O) (g : M ->* N) : mapDomainBialgHom R (f.comp g) = (mapDomainBialgHom R f).comp
 (mapDomainBialgHom R g)
· 使用引理 `MonoidAlgebra.mapDomainBialgHom_mapDomainOfBialgHom`：mapDomainBialgHom_m
apDomainOfBialgHom (f : R[G] ->ₐc[R] R[H]) : mapDomainBialgHom R (mapDomainOfBia
lgHom f) = f
-/
lemma mapDomainOfBialgHom_comp (f : R[H] →ₐc[R] R[I]) (g : R[G] →ₐc[R] R[H]) :
    mapDomainOfBialgHom (f.comp g) = (mapDomainOfBialgHom f).comp (mapDomainOfBialgHom g) := by
  rw [← mapDomainOfBialgHom_mapDomainBialgHom (R := R)
    ((mapDomainOfBialgHom f).comp (mapDomainOfBialgHom g)),
    mapDomainBialgHom_comp, mapDomainBialgHom_mapDomainOfBialgHom,
    mapDomainBialgHom_mapDomainOfBialgHom]

/-- The equivalence between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group algebras
over a domain. -/
@[expose, to_additive (attr := simps)
/-- The equivalence between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group algebras
over a domain. -/]
/-
**MonoidAlgebra.mapDomainBialgHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`
。
形式化陈述：mapDomainBialgHomEquiv : (G ->* H) ≃ (R[G] ->ₐc[R] R[H]) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.mapDomainOfBialgHom_mapDomainBialgHom`：mapDomainOfBialgHom
_mapDomainBialgHom (f : G ->* H) : mapDomainOfBialgHom (mapDomainBialgHom (R
· 使用引理 `MonoidAlgebra.mapDomainBialgHom_mapDomainOfBialgHom`：mapDomainBialgHom_m
apDomainOfBialgHom (f : R[G] ->ₐc[R] R[H]) : mapDomainBialgHom R (mapDomainOfBia
lgHom f) = f
-/
def mapDomainBialgHomEquiv : (G →* H) ≃ (R[G] →ₐc[R] R[H]) where
  toFun := mapDomainBialgHom R
  invFun := mapDomainOfBialgHom
  left_inv := mapDomainOfBialgHom_mapDomainBialgHom
  right_inv := mapDomainBialgHom_mapDomainOfBialgHom

end Group

section CommGroup
variable [CommGroup G] [CommGroup H]

/-- The group isomorphism between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group
algebras over a domain. -/
@[expose, simps!]
/-
**MonoidAlgebra.mapDomainBialgHomMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgeb
ra`。
形式化陈述：mapDomainBialgHomMulEquiv : (G ->* H) ≃* WithConv (R[G] ->ₐc[R] R[H]) wher
e toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The group isomorphism between group homs `G → H` and bialgebra homs `R[G] → R[H]
` of group
algebras over a domain.
-/
def mapDomainBialgHomMulEquiv : (G →* H) ≃* WithConv (R[G] →ₐc[R] R[H]) where
  toEquiv := mapDomainBialgHomEquiv.trans (WithConv.equiv _).symm
  map_mul' f g := by simp

end CommGroup
end CommRing
end MonoidAlgebra

namespace AddMonoidAlgebra
section CommSemiring
variable [CommSemiring R] [CommSemiring S]

section Semiring
variable [Semiring A] [Semiring B] [Bialgebra R A] [Bialgebra R B] [AddMonoid M] [AddMonoid N]

/-- See note [partially-applied ext lemmas]. -/
/-
**AddMonoidAlgebra.bialgHom_ext'** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：bialgHom_ext' ⦃φ₁ φ₂ : A[M] ->ₐc[R] B⦄ (single_one_right : (φ₁ : A[M] ->* 
B).comp (of A M) = (φ₂ : A[M] ->* B).comp (of A M)) (single_one_left : (φ₁ : A[M
] ->ₐ[R] B).comp singleZeroAlgHom = (φ₂ : A[M] ->ₐ[R] B).comp singleZeroAlgHom) 
: φ₁ = φ₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHomClass.toMonoidHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `BialgHom.coe_toAlgHom_injective`：coe_toAlgHom_injective : Function.Injec
tive ((↑) : (A ->ₐc[R] B) -> A ->ₐ[R] B)
· 使用引理 `AddMonoidAlgebra.algHom_ext'`：algHom_ext' ⦃φ₁ φ₂ : A[M] ->ₐ[R] B⦄ (singl
e_one_right : (φ₁ : A[M] ->* B).comp (of A M) = (φ₂ : A[M] ->* B).comp (of A M))
 (single_one_left …

--- 原说明 ---
See note [partially-applied ext lemmas].
-/
lemma bialgHom_ext' ⦃φ₁ φ₂ : A[M] →ₐc[R] B⦄
    (single_one_right : (φ₁ : A[M] →* B).comp (of A M) = (φ₂ : A[M] →* B).comp (of A M))
    (single_one_left : (φ₁ : A[M] →ₐ[R] B).comp singleZeroAlgHom =
      (φ₂ : A[M] →ₐ[R] B).comp singleZeroAlgHom) : φ₁ = φ₂ :=
  BialgHom.coe_toAlgHom_injective <| algHom_ext' single_one_right single_one_left
/-
**AddMonoidAlgebra.isGroupLikeElem_of** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidAlgebr
a`。
形式化陈述：isGroupLikeElem_of (m : M) : IsGroupLikeElem R (of A M m)
参数：m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.isGroupLikeElem_single_one`：∀ {R : Type u_1} {A : Type 
u_3} {G : Type u_5} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Bial
gebra R A]   (g : G), IsGroupLike…
-/
lemma isGroupLikeElem_of (m : M) : IsGroupLikeElem R (of A M m) := isGroupLikeElem_single_one ..

variable (R A M) in
/-- The bialgebra equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms of
`Multiplicative`. -/
-- TODO: Make `BialgEquiv.toCoalgEquiv` the simp normal form so that this can be simp
@[expose, simps! -isSimp]
/-
**AddMonoidAlgebra.toMultiplicativeBialgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddMono
idAlgebra`。
形式化陈述：toMultiplicativeBialgEquiv : A[M] ≃ₐc[R] MonoidAlgebra A (Multiplicative M
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toMultiplicativeBialgEquiv : A[M] ≃ₐc[R] MonoidAlgebra A (Multiplicative M) :=
  .ofAlgEquiv (toMultiplicativeAlgEquiv R A M) (by ext <;> simp) <| by
    ext a
    · simp
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

@[simp]
/-
**AddMonoidAlgebra.toMultiplicativeBialgEquiv_single** 是 Mathlib 中的一个引理，位于命名空间 `
AddMonoidAlgebra`。
形式化陈述：toMultiplicativeBialgEquiv_single (m : M) (a : A) : toMultiplicativeBialgE
quiv R A M (single m a) = .single (.ofAdd m) a
参数：m : M；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BialgEquiv.ofAlgEquiv_apply`：∀ {R : Type u} {A : Type v} {B : Type w} [i
nst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Bi
algebra R A] [ins…
· 使用引理 `AddMonoidAlgebra.toMultiplicativeAlgEquiv_single`：toMultiplicativeAlgEqu
iv_single (m : M) (a : A) : toMultiplicativeAlgEquiv R A M (single m a) = .singl
e (.ofAdd m) a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toMultiplicativeBialgEquiv_single (m : M) (a : A) :
    toMultiplicativeBialgEquiv R A M (single m a) = .single (.ofAdd m) a := by
  simp [toMultiplicativeBialgEquiv]

end Semiring

section CommSemiring
variable [CommSemiring A] [Algebra R A] [AddMonoid M]

variable (R M A) in
/-- `AddMonoidAlgebra.lift` as a `MulEquiv`. -/
/-
**AddMonoidAlgebra.liftMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：liftMulEquiv : (Multiplicative M ->* A) ≃* WithConv (R[M] ->ₐ[R] A) where 
toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`AddMonoidAlgebra.lift` as a `MulEquiv`.
-/
def liftMulEquiv : (Multiplicative M →* A) ≃* WithConv (R[M] →ₐ[R] A) where
  toEquiv := (lift R A M).trans (WithConv.equiv _).symm
  map_mul' f g := by ext; simp [AlgHom.convMul_apply]

end CommSemiring

section AddCommMonoid
variable [AddCommMonoid M] [AddCommMonoid N]

/-
**AddMonoidAlgebra.comulAlgHom_comp_mapRingHom** 是 Mathlib 中的一个引理，位于命名空间 `AddMon
oidAlgebra`。
形式化陈述：comulAlgHom_comp_mapRingHom (f : R ->+* S) : (comulAlgHom S S[M]).toRingHo
m.comp (mapRingHom M f) = .comp (Algebra.TensorProduct.mapRingHom f (mapRingHom 
M f) (mapRingHom M f) (by ext; simp) (by ext; simp)) (comulAlgHom R R[M]).toRing
Hom
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ringHom_ext'`：ringHom_ext' [Semiring S] [AddMonoid M] {
f g : R[M] ->+* S} (h₁ : f.comp singleZeroRingHom = g.comp singleZeroRingHom) (h
_of : (f : R[M] ->*…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.singleZeroRingHom_apply`：∀ {R : Type u_1} {M : Type u_4
} [inst : Semiring R] [inst_1 : AddZeroClass M] (a : R),   AddMonoidAlgebra.sing
leZeroRingHom a = (↑(AddMonoid…
· 使用定理 `AddMonoidAlgebra.singleAddHom_apply`：∀ {R : Type u_1} {M : Type u_4} [in
st : Semiring R] (m : M) (r : R),   (AddMonoidAlgebra.singleAddHom m) r = AddMon
oidAlgebra.single m r
· 使用定理 `AddMonoidAlgebra.mapRingHom_single`：∀ {R : Type u_3} {S : Type u_4} {M :
 Type u_6} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : AddMonoid M]   (f
 : R →+* S) (a : M) (b :…
· 使用定理 `Bialgebra.comulAlgHom_apply`：∀ (R : Type u) (A : Type v) [inst : CommSem
iring R] [inst_1 : Semiring A] [inst_2 : Bialgebra R A] (a : A),   (Bialgebra.co
mulAlgHom R A) a …
· 使用定理 `AddMonoidAlgebra.comul_single`：∀ {R : Type u_1} [inst : CommSemiring R] 
{A : Type u_2} [inst_1 : Semiring A] {X : Type u_3}   [inst_2 : _root_.Module R 
A] [inst_3 : Coalge…
· 使用引理 `Algebra.TensorProduct.mapRingHom_tmul`：mapRingHom_tmul (s : S) (t : T) :
 mapRingHom fR fS fT HS HT (s otimesₜ t) = fS s otimesₜ fT t
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Multiplicative.monoidHom_ext`：Multiplicative.monoidHom_ext [AddZeroClass
 α] [MulOneClass β] (f g : Multiplicative α ->* β) (h : f.toAdditiveRight = g.to
AdditiveRight) : f…
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Additive.ext`：∀ {α : Type u} {a b : Additive α}, Additive.toMul a = Addi
tive.toMul b → a = b
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `MonoidHom.toAdditiveRight_apply_apply`：∀ {α : Type u_3} {β : Type u_4} [
inst : AddZeroClass α] [inst_1 : MulOneClass β] (a : Multiplicative α →* β) (a_1
 : α),   (MonoidHom.toAddit…
· 使用定理 `IsGroupLikeElem.comul_eq_tmul_self`：∀ {R : Type u_2} {A : Type u_3} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [i
nst_3 : Coalgebra R A] {…
-/
lemma comulAlgHom_comp_mapRingHom (f : R →+* S) :
    (comulAlgHom S S[M]).toRingHom.comp (mapRingHom M f) =
      .comp (Algebra.TensorProduct.mapRingHom f (mapRingHom M f) (mapRingHom M f)
        (by ext; simp) (by ext; simp))
        (comulAlgHom R R[M]).toRingHom := by ext <;> simp
/-
**AddMonoidAlgebra.counitAlgHom_comp_mapRingHom** 是 Mathlib 中的一个引理，位于命名空间 `AddMo
noidAlgebra`。
形式化陈述：counitAlgHom_comp_mapRingHom (f : R ->+* S) : (counitAlgHom S S[M]).toRing
Hom.comp (mapRingHom M f) = f.comp (counitAlgHom R R[M]).toRingHom
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ringHom_ext'`：ringHom_ext' [Semiring S] [AddMonoid M] {
f g : R[M] ->+* S} (h₁ : f.comp singleZeroRingHom = g.comp singleZeroRingHom) (h
_of : (f : R[M] ->*…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.singleZeroRingHom_apply`：∀ {R : Type u_1} {M : Type u_4
} [inst : Semiring R] [inst_1 : AddZeroClass M] (a : R),   AddMonoidAlgebra.sing
leZeroRingHom a = (↑(AddMonoid…
· 使用定理 `AddMonoidAlgebra.singleAddHom_apply`：∀ {R : Type u_1} {M : Type u_4} [in
st : Semiring R] (m : M) (r : R),   (AddMonoidAlgebra.singleAddHom m) r = AddMon
oidAlgebra.single m r
· 使用定理 `AddMonoidAlgebra.mapRingHom_single`：∀ {R : Type u_3} {S : Type u_4} {M :
 Type u_6} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : AddMonoid M]   (f
 : R →+* S) (a : M) (b :…
· 使用定理 `Bialgebra.counitAlgHom_apply`：∀ (R : Type u) (A : Type v) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Bialgebra R A] (a : A),   (Bialgebra.c
ounitAlgHom R A) a…
· 使用定理 `AddMonoidAlgebra.counit_single`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] {X : Type u_3}   [inst_2 : _root_.Module R
 A] [inst_3 : Coalge…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Multiplicative.monoidHom_ext`：Multiplicative.monoidHom_ext [AddZeroClass
 α] [MulOneClass β] (f g : Multiplicative α ->* β) (h : f.toAdditiveRight = g.to
AdditiveRight) : f…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Additive.ext`：∀ {α : Type u} {a b : Additive α}, Additive.toMul a = Addi
tive.toMul b → a = b
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `MonoidHom.toAdditiveRight_apply_apply`：∀ {α : Type u_3} {β : Type u_4} [
inst : AddZeroClass α] [inst_1 : MulOneClass β] (a : Multiplicative α →* β) (a_1
 : α),   (MonoidHom.toAddit…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `IsGroupLikeElem.counit_eq_one`：∀ {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3
 : Coalgebra R A] {…
-/
lemma counitAlgHom_comp_mapRingHom (f : R →+* S) :
    (counitAlgHom S S[M]).toRingHom.comp (mapRingHom M f) =
      f.comp (counitAlgHom R R[M]).toRingHom := by ext <;> simp

end AddCommMonoid
end CommSemiring

section CommRing
variable [CommRing R] [IsDomain R]

section AddZeroClass
variable [AddZeroClass M] {x : R[M]}

/-
**AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_of** 是 Mathlib 中的一个引理，位于命名空间 `A
ddMonoidAlgebra`。
形式化陈述：isGroupLikeElem_iff_mem_range_of : IsGroupLikeElem R x ↔ x in Set.range (o
f R M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one`：∀ {R : Type u
_1} {M : Type u_8} [inst : CommRing R] [IsDomain R] {x : AddMonoidAlgebra R M}, 
  IsGroupLikeElem R x ↔ x ∈ Set.range fun x => …
-/
lemma isGroupLikeElem_iff_mem_range_of : IsGroupLikeElem R x ↔ x ∈ Set.range (of R M) :=
  isGroupLikeElem_iff_mem_range_single_one

end AddZeroClass

section AddCommGroup
variable [AddCommGroup G] [AddCommGroup H]

/-- The group isomorphism between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group
algebras over a domain. -/
/-
**AddMonoidAlgebra.mapDomainBialgHomAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoi
dAlgebra`。
形式化陈述：mapDomainBialgHomAddEquiv : (G ->+ H) ≃+ Additive (WithConv <| R[G] ->ₐc[R
] R[H]) where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The group isomorphism between group homs `G → H` and bialgebra homs `R[G] → R[H]
` of group
algebras over a domain.
-/
def mapDomainBialgHomAddEquiv : (G →+ H) ≃+ Additive (WithConv <| R[G] →ₐc[R] R[H]) where
  toEquiv := mapDomainBialgHomEquiv.trans <| (WithConv.equiv _).symm.trans Additive.ofMul
  map_add' f g := by simp

end AddCommGroup
end CommRing
end AddMonoidAlgebra

namespace LaurentPolynomial

open AddMonoidAlgebra

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Bialgebra R A]

/-
**LaurentPolynomial.instBialgebra** 是 Mathlib 中的一个实例，位于命名空间 `LaurentPolynomial`。
形式化陈述：instBialgebra : Bialgebra R A[T;T⁻¹]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBialgebra : Bialgebra R A[T;T⁻¹] :=
  inferInstanceAs <| Bialgebra R A[ℤ]

@[simp]
/-
**LaurentPolynomial.comul_T** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：comul_T (n : Int) : comul (T n : A[T;T⁻¹]) = T n otimesₜ[R] T n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsGroupLikeElem.comul_eq_tmul_self`：∀ {R : Type u_2} {A : Type u_3} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [i
nst_3 : Coalgebra R A] {…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comul_T (n : ℤ) : comul (T n : A[T;T⁻¹]) = T n ⊗ₜ[R] T n := by simp [T, -single_eq_C_mul_T]

@[simp]
/-
**LaurentPolynomial.counit_T** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：counit_T (n : Int) : Coalgebra.counit (R
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsGroupLikeElem.counit_eq_one`：∀ {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3
 : Coalgebra R A] {…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem counit_T (n : ℤ) :
    Coalgebra.counit (R := R) (T n : A[T;T⁻¹]) = 1 := by
  simp [T, -single_eq_C_mul_T]

end LaurentPolynomial

