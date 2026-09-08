/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jung Tao Cheng, Christian Merten, Andrew Yang
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Submersive presentations

In this file we define `PreSubmersivePresentation`. This is a presentation `P` that has
fewer relations than generators. More precisely there exists an injective map from `σ`
to `ι`. To such a presentation we may associate a Jacobian. `P` is then a submersive
presentation, if its Jacobian is invertible.

Algebras that admit such a presentation are called standard smooth. See
`Mathlib.RingTheory.Smooth.StandardSmooth` for applications.

## Main definitions

All of these are in the `Algebra` namespace. Let `S` be an `R`-algebra.

- `PreSubmersivePresentation`: A `Presentation` of `S` as `R`-algebra, equipped with an injective
  map `P.map` from `σ` to `ι`. This map is used to define the differential of a
  presubmersive presentation.

For a presubmersive presentation `P` of `S` over `R` we make the following definitions:

- `PreSubmersivePresentation.differential`: A linear endomorphism of `σ → P.Ring` sending
  the `j`-th standard basis vector, corresponding to the `j`-th relation, to the vector
  of partial derivatives of `P.relation j` with respect to the coordinates `P.map i` for
  `i : σ`.
- `PreSubmersivePresentation.jacobian`: The determinant of `P.differential`.
- `PreSubmersivePresentation.jacobiMatrix`: If `σ` has a `Fintype` instance, we may form
  the matrix corresponding to `P.differential`. Its determinant is `P.jacobian`.
- `SubmersivePresentation`: A submersive presentation is a finite, presubmersive presentation `P`
  with in `S` invertible Jacobian.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry"
in June 2024.

-/

@[expose] public section

universe t t' w w' u v

open TensorProduct Module MvPolynomial

namespace Algebra

variable (R : Type u) (S : Type v) (ι : Type w) (σ : Type t) [CommRing R] [CommRing S] [Algebra R S]

/--
A `PreSubmersivePresentation` of an `R`-algebra `S` is a `Presentation`
with relations equipped with an injective `map : relations → vars`.

This map determines how the differential of `P` is constructed. See
`PreSubmersivePresentation.differential` for details.
-/
/-
**Algebra.PreSubmersivePresentation** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u) →   (S : Type v) →     Type w → Type t → [inst : CommRing R] 
→ [inst_1 : CommRing S] → [Algebra R S] → Type (max (max (max t u) v) w)
参数：max (max t u) v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `PreSubmersivePresentation` of an `R`-algebra `S` is a `Presentation`
with relations equipped with an injective `map : relations → vars`.

This map determines how the differential of `P` is constructed. See
`PreSubmersivePresentation.differential` for details.
-/
structure PreSubmersivePresentation extends Algebra.Presentation R S ι σ where
  /-- A map from the relations type to the variables type. Used to compute the differential. -/
  map : σ → ι
  map_inj : Function.Injective map

namespace PreSubmersivePresentation

variable {R S ι σ}
variable (P : PreSubmersivePresentation R S ι σ)

include P in
/-
**Algebra.PreSubmersivePresentation.card_relations_le_card_vars_of_isFinite** 是 
Mathlib 中的一个引理，位于命名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：card_relations_le_card_vars_of_isFinite [Finite ι] : Nat.card σ <= Nat.car
d ι
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.card_le_card_of_injective`：card_le_card_of_injective {α : Type u} {β
 : Type v} [Finite β] (f : α -> β) (hf : Injective f) : Nat.card α <= Nat.card β
· 使用定理 `Algebra.PreSubmersivePresentation.map_inj`：∀ {R : Type u} {S : Type v} {
ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Alg
ebra R S]   (self : Algebra.Pre…
-/
lemma card_relations_le_card_vars_of_isFinite [Finite ι] :
    Nat.card σ ≤ Nat.card ι :=
  Nat.card_le_card_of_injective P.map P.map_inj

section

variable [Finite σ]

/-- The standard basis of `σ → P.ring`. -/
/-
**Algebra.PreSubmersivePresentation.basis** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra.P
reSubmersivePresentation`。
形式化陈述：basis : Basis σ P.Ring (σ -> P.Ring)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard basis of `σ → P.ring`.
-/
noncomputable abbrev basis : Basis σ P.Ring (σ → P.Ring) :=
  Pi.basisFun P.Ring σ

/--
The differential of a `P : PreSubmersivePresentation` is a `P.Ring`-linear map on
`σ → P.Ring`:

The `j`-th standard basis vector, corresponding to the `j`-th relation of `P`, is mapped
to the vector of partial derivatives of `P.relation j` with respect
to the coordinates `P.map i` for all `i : σ`.

The determinant of this map is the Jacobian of `P` used to define when a `PreSubmersivePresentation`
is submersive. See `PreSubmersivePresentation.jacobian`.
-/
/-
**Algebra.PreSubmersivePresentation.differential** 是 Mathlib 中的一个定义，位于命名空间 `Alge
bra.PreSubmersivePresentation`。
形式化陈述：differential : (σ -> P.Ring) ->ₗ[P.Ring] (σ -> P.Ring)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The differential of a `P : PreSubmersivePresentation` is a `P.Ring`-linear map o
n
`σ → P.Ring`:

The `j`-th standard basis vector, corresponding to the `j`-th relation of `P`, i
s mapped
to the vector of partial derivatives of `P.relation j` with respect
to the coordinates `P.map i` for all `i : σ`.

The determinant of this map is the Jacobian of `P` used to define when a `PreSub
mersivePresentation`
is submersive. See `PreSubmersivePresentation.jacobian`.
-/
noncomputable def differential : (σ → P.Ring) →ₗ[P.Ring] (σ → P.Ring) :=
  Basis.constr P.basis P.Ring
    (fun j i : σ ↦ MvPolynomial.pderiv (P.map i) (P.relation j))

/-- `PreSubmersivePresentation.differential` pushed forward to `S` via `aeval P.val`. -/
/-
**Algebra.PreSubmersivePresentation.aevalDifferential** 是 Mathlib 中的一个定义，位于命名空间 
`Algebra.PreSubmersivePresentation`。
形式化陈述：aevalDifferential : (σ -> S) ->ₗ[S] (σ -> S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PreSubmersivePresentation.differential` pushed forward to `S` via `aeval P.val`
.
-/
noncomputable def aevalDifferential : (σ → S) →ₗ[S] (σ → S) :=
  (Pi.basisFun S σ).constr S
    (fun j i : σ ↦ aeval P.val <| pderiv (P.map i) (P.relation j))

@[simp]
/-
**Algebra.PreSubmersivePresentation.aevalDifferential_single** 是 Mathlib 中的一个引理，
位于命名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：aevalDifferential_single [DecidableEq σ] (i j : σ) : P.aevalDifferential (
Pi.single i 1) j = aeval P.val (pderiv (P.map j) (P.relation i))
参数：i j : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.basisFun_apply`：basisFun_apply [DecidableEq η] (i) : basisFun R η i =
 Pi.single i 1
· 使用定理 `Module.Basis.constr_basis`：constr_basis (f : ι -> M') (i : ι) : (constr 
(M'
-/
lemma aevalDifferential_single [DecidableEq σ] (i j : σ) :
    P.aevalDifferential (Pi.single i 1) j = aeval P.val (pderiv (P.map j) (P.relation i)) := by
  dsimp only [aevalDifferential]
  rw [← Pi.basisFun_apply, Basis.constr_basis]

/-- The Jacobian of a `P : PreSubmersivePresentation` is the determinant
of `P.differential` viewed as element of `S`. -/
/-
**Algebra.PreSubmersivePresentation.jacobian** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.
PreSubmersivePresentation`。
形式化陈述：jacobian : S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Jacobian of a `P : PreSubmersivePresentation` is the determinant
of `P.differential` viewed as element of `S`.
-/
noncomputable def jacobian : S :=
  algebraMap P.Ring S <| LinearMap.det P.differential

end

section Matrix

variable [Fintype σ] [DecidableEq σ]

/--
If `σ` has a `Fintype` and `DecidableEq` instance, the differential of `P`
can be expressed in matrix form.
-/
/-
**Algebra.PreSubmersivePresentation.jacobiMatrix** 是 Mathlib 中的一个定义，位于命名空间 `Alge
bra.PreSubmersivePresentation`。
形式化陈述：jacobiMatrix : Matrix σ σ P.Ring
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `σ` has a `Fintype` and `DecidableEq` instance, the differential of `P`
can be expressed in matrix form.
-/
noncomputable def jacobiMatrix : Matrix σ σ P.Ring :=
  LinearMap.toMatrix P.basis P.basis P.differential
/-
**Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det** 是 Mathlib 中的一
个引理，位于命名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：jacobian_eq_jacobiMatrix_det : P.jacobian = algebraMap P.Ring S P.jacobiMa
trix.det
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.Generators.algebraMap_apply`：algebraMap_apply (x) : algebraMap P
.Ring S x = aeval (R
· 使用定理 `LinearMap.det_toMatrix'`：det_toMatrix' {ι : Type*} [Fintype ι] [Decidabl
eEq ι] (f : (ι -> A) ->ₗ[A] ι -> A) : Matrix.det (LinearMap.toMatrix' f) = Linea
rMap.det f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma jacobian_eq_jacobiMatrix_det : P.jacobian = algebraMap P.Ring S P.jacobiMatrix.det := by
  simp [jacobiMatrix, jacobian]
/-
**Algebra.PreSubmersivePresentation.jacobiMatrix_apply** 是 Mathlib 中的一个引理，位于命名空间
 `Algebra.PreSubmersivePresentation`。
形式化陈述：jacobiMatrix_apply (i j : σ) : P.jacobiMatrix i j = MvPolynomial.pderiv (P
.map i) (P.relation j)
参数：i j : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `LinearEquiv.arrowCongr.congr_simp`：∀ {R₁ : Type u_9} {R₂ : Type u_10} {R
₁' : Type u_12} {R₂' : Type u_13} {M₁ : Type u_17} {M₂ : Type u_18}   {M₁' : Typ
e u_20} {M₂' : Type u_2…
· 使用定理 `Pi.basisFun_equivFun`：basisFun_equivFun : (Pi.basisFun R η).equivFun = L
inearEquiv.refl _ _
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Basis.constr_apply_fintype`：constr_apply_fintype [Fintype ι] (b :
 Basis ι R M) (f : ι -> M') (x : M) : (constr (M'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Fintype.sum_single_smul`：sum_single_smul {R : Type*} [Semiring R] [Modul
e R α] (f : ι -> α) (r : R) (i₀ : ι) : ∑ i, (Pi.single (M
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma jacobiMatrix_apply (i j : σ) :
    P.jacobiMatrix i j = MvPolynomial.pderiv (P.map i) (P.relation j) := by
  simp [jacobiMatrix, LinearMap.toMatrix, differential, basis]
/-
**Algebra.PreSubmersivePresentation.aevalDifferential_toMatrix'_eq_mapMatrix_jac
obiMatrix** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：∀ {R : Type u} {S : Type v} {ι : Type w} {σ : Type t} [inst : CommRing R] 
[inst_1 : CommRing S] [inst_2 : Algebra R S]   (P : Algebra.PreSubmersivePresent
ation R S ι σ) [inst_3 : Fintype σ] [inst_4 : DecidableEq σ],   LinearMap.toMatr
ix' P.aevalDifferential = (MvPolynomial.aeval P.val).mapMatrix P.jacobiMatrix
参数：P : Algebra.PreSubmersivePresentation R S ι σ；MvPolynomial.aeval P.val。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.toMatrix_eq_toMatrix'`：∀ {R : Type u_1} [inst : CommSemiring R
] {n : Type u_4} [inst_1 : Fintype n] [inst_2 : DecidableEq n],   LinearMap.toMa
trix (Pi.basisFun R n…
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.basisFun_apply`：basisFun_apply [DecidableEq η] (i) : basisFun R η i =
 Pi.single i 1
· 使用定理 `Pi.basisFun_repr`：basisFun_repr (x : η -> R) (i : η) : (Pi.basisFun R η)
.repr x i = x i
· 使用引理 `Algebra.PreSubmersivePresentation.aevalDifferential_single`：aevalDiffere
ntial_single [DecidableEq σ] (i j : σ) : P.aevalDifferential (Pi.single i 1) j =
 aeval P.val (pderiv (P.map j) (P.relation i))
· 使用定理 `AlgHom.mapMatrix_apply`：∀ {m : Type u_2} {R : Type u_7} {α : Type u_11} 
{β : Type u_12} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : CommSemi
ring R] [ins…
· 使用引理 `Algebra.PreSubmersivePresentation.jacobiMatrix_apply`：jacobiMatrix_apply
 (i j : σ) : P.jacobiMatrix i j = MvPolynomial.pderiv (P.map i) (P.relation j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix :
    P.aevalDifferential.toMatrix' = (aeval P.val).mapMatrix P.jacobiMatrix := by
  ext i j : 1
  rw [← LinearMap.toMatrix_eq_toMatrix']
  rw [LinearMap.toMatrix_apply]
  simp [jacobiMatrix_apply]

end Matrix

section

variable [Finite σ]

/-
**Algebra.PreSubmersivePresentation.jacobian_eq_det_aevalDifferential** 是 Mathli
b 中的一个引理，位于命名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：jacobian_eq_det_aevalDifferential : P.jacobian = P.aevalDifferential.det
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det`：jacobian
_eq_jacobiMatrix_det : P.jacobian = algebraMap P.Ring S P.jacobiMatrix.det
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.Generators.algebraMap_eq`：∀ {R : Type u} {S : Type v} {ι : Type 
w} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (self : Al
gebra.Generators R S ι…
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `Algebra.PreSubmersivePresentation.aevalDifferential_toMatrix'_eq_mapMatr
ix_jacobiMatrix`：∀ {R : Type u} {S : Type v} {ι : Type w} {σ : Type t} [inst : C
ommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (P : Algebra.PreSub…
· 使用定理 `AlgHom.mapMatrix_apply`：∀ {m : Type u_2} {R : Type u_7} {α : Type u_11} 
{β : Type u_12} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : CommSemi
ring R] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma jacobian_eq_det_aevalDifferential : P.jacobian = P.aevalDifferential.det := by
  classical
  cases nonempty_fintype σ
  simp [← LinearMap.det_toMatrix', P.aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix,
    jacobian_eq_jacobiMatrix_det, RingHom.map_det, P.algebraMap_eq]
/-
**Algebra.PreSubmersivePresentation.isUnit_jacobian_iff_aevalDifferential_biject
ive** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：isUnit_jacobian_iff_aevalDifferential_bijective : IsUnit P.jacobian ↔ Func
tion.Bijective P.aevalDifferential
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.PreSubmersivePresentation.jacobian_eq_det_aevalDifferential`：jac
obian_eq_det_aevalDifferential : P.jacobian = P.aevalDifferential.det
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.isUnit_iff_isUnit_det`：isUnit_iff_isUnit_det [Module.Finite R 
M] [Module.Free R M] (f : M ->ₗ[R] M) : IsUnit f ↔ IsUnit f.det
· 使用定理 `Module.Free.function`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Fini
te ι] [Mod…
· 使用定理 `Module.End.isUnit_iff`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M
), IsUnit f…
-/
lemma isUnit_jacobian_iff_aevalDifferential_bijective :
    IsUnit P.jacobian ↔ Function.Bijective P.aevalDifferential := by
  rw [P.jacobian_eq_det_aevalDifferential, ← LinearMap.isUnit_iff_isUnit_det]
  exact Module.End.isUnit_iff P.aevalDifferential
/-
**Algebra.PreSubmersivePresentation.isUnit_jacobian_of_linearIndependent_of_span
_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：isUnit_jacobian_of_linearIndependent_of_span_eq_top (hli : LinearIndepende
nt S (fun j i : σ => aeval P.val <| pderiv (P.map i) (P.relation j))) (hsp : Sub
module.span S (Set.range <| (fun j i : σ => aeval P.val <| pderiv (P.map i) (P.r
elation j))) = ⊤) : IsUnit P.jacobian
参数：hli : LinearIndependent S (fun j i : σ => aeval P.val <| pderiv (P.map i) (P.
relation j))；hsp : Submodule.span S (Set.range <| (fun j i : σ => aeval P.val <|
 pderiv (P.map i) (P.relation j))) = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.PreSubmersivePresentation.isUnit_jacobian_iff_aevalDifferential_
bijective`：isUnit_jacobian_iff_aevalDifferential_bijective : IsUnit P.jacobian ↔
 Function.Bijective P.aevalDifferential
· 使用引理 `LinearMap.bijective_of_linearIndependent_of_span_eq_top`：LinearMap.bijec
tive_of_linearIndependent_of_span_eq_top {N : Type*} [AddCommGroup N] [Module R 
N] {f : M ->ₗ[R] N} {ι : Type*} {v : ι -> M} …
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.basisFun_apply`：basisFun_apply [DecidableEq η] (i) : basisFun R η i =
 Pi.single i 1
· 使用引理 `Algebra.PreSubmersivePresentation.aevalDifferential_single`：aevalDiffere
ntial_single [DecidableEq σ] (i j : σ) : P.aevalDifferential (Pi.single i 1) j =
 aeval P.val (pderiv (P.map j) (P.relation i))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
lemma isUnit_jacobian_of_linearIndependent_of_span_eq_top
    (hli : LinearIndependent S (fun j i : σ ↦ aeval P.val <| pderiv (P.map i) (P.relation j)))
    (hsp : Submodule.span S
      (Set.range <| (fun j i : σ ↦ aeval P.val <| pderiv (P.map i) (P.relation j))) = ⊤) :
    IsUnit P.jacobian := by
  classical
  rw [isUnit_jacobian_iff_aevalDifferential_bijective]
  exact LinearMap.bijective_of_linearIndependent_of_span_eq_top (Pi.basisFun _ _).span_eq
    (by convert! hli; simp) (by convert! hsp; simp)

end

section Constructions

/-- Transport a pre-submersive presentation along an algebra isomorphism. -/
@[simps toPresentation map]
/-
**Algebra.PreSubmersivePresentation.ofAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
a.PreSubmersivePresentation`。
形式化陈述：ofAlgEquiv (P : PreSubmersivePresentation R S ι σ) {T : Type*} [CommRing T
] [Algebra R T] (e : S ≃ₐ[R] T) : PreSubmersivePresentation R T ι σ where __
参数：P : PreSubmersivePresentation R S ι σ；e : S ≃ₐ[R] T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.PreSubmersivePresentation.map_inj`：∀ {R : Type u} {S : Type v} {
ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Alg
ebra R S]   (self : Algebra.Pre…

--- 原说明 ---
Transport a pre-submersive presentation along an algebra isomorphism.
-/
noncomputable def ofAlgEquiv
    (P : PreSubmersivePresentation R S ι σ) {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T) :
    PreSubmersivePresentation R T ι σ where
  __ := P.toPresentation.ofAlgEquiv e
  map := P.map
  map_inj := P.map_inj

@[simp]
/-
**Algebra.PreSubmersivePresentation.jacobiMatrix_ofAlgEquiv** 是 Mathlib 中的一个引理，位
于命名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：jacobiMatrix_ofAlgEquiv (P : PreSubmersivePresentation R S ι σ) {T : Type*
} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T) [Fintype σ] [DecidableEq σ] : (P.of
AlgEquiv e).jacobiMatrix = P.jacobiMatrix
参数：P : PreSubmersivePresentation R S ι σ；e : S ≃ₐ[R] T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma jacobiMatrix_ofAlgEquiv (P : PreSubmersivePresentation R S ι σ) {T : Type*} [CommRing T]
    [Algebra R T] (e : S ≃ₐ[R] T) [Fintype σ] [DecidableEq σ] :
    (P.ofAlgEquiv e).jacobiMatrix = P.jacobiMatrix :=
  rfl

@[simp]
/-
**Algebra.PreSubmersivePresentation.jacobian_ofAlgEquiv** 是 Mathlib 中的一个引理，位于命名空
间 `Algebra.PreSubmersivePresentation`。
形式化陈述：jacobian_ofAlgEquiv (P : PreSubmersivePresentation R S ι σ) {T : Type*} [C
ommRing T] [Algebra R T] (e : S ≃ₐ[R] T) [Finite σ] : (P.ofAlgEquiv e).jacobian 
= e P.jacobian
参数：P : PreSubmersivePresentation R S ι σ；e : S ≃ₐ[R] T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det`：jacobian
_eq_jacobiMatrix_det : P.jacobian = algebraMap P.Ring S P.jacobiMatrix.det
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Algebra.Generators.algebraMap_apply`：algebraMap_apply (x) : algebraMap P
.Ring S x = aeval (R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.PreSubmersivePresentation.ofAlgEquiv_toPresentation`：∀ {R : Type
 u} {S : Type v} {ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRin
g S] [inst_2 : Algebra R S]   (P : Algebra.PreSub…
· 使用定理 `Algebra.Presentation.ofAlgEquiv_toGenerators`：∀ {R : Type u} {S : Type v
} {ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : 
Algebra R S]   (P : Algebra.Presen…
· 使用引理 `MvPolynomial.comp_aeval_apply`：comp_aeval_apply {B : Type*} [CommSemirin
g B] [Algebra R B] (φ : S₁ ->ₐ[R] B) (p : MvPolynomial σ R) : φ (aeval f p) = ae
val (fun i => φ (f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma jacobian_ofAlgEquiv (P : PreSubmersivePresentation R S ι σ) {T : Type*} [CommRing T]
    [Algebra R T] (e : S ≃ₐ[R] T) [Finite σ] :
    (P.ofAlgEquiv e).jacobian = e P.jacobian := by
  classical
  cases nonempty_fintype σ
  rw [jacobian_eq_jacobiMatrix_det, jacobian_eq_jacobiMatrix_det]
  simp only [ofAlgEquiv_toPresentation, Presentation.ofAlgEquiv_toGenerators,
    jacobiMatrix_ofAlgEquiv, Generators.algebraMap_apply, Generators.ofAlgEquiv_val,
    ← AlgHom.coe_coe e, MvPolynomial.comp_aeval_apply]
  simp [Function.comp_def]

/-- If `algebraMap R S` is bijective, the empty generators are a pre-submersive
presentation with no relations. -/
/-
**Algebra.PreSubmersivePresentation.ofBijectiveAlgebraMap** 是 Mathlib 中的一个定义，位于命
名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：ofBijectiveAlgebraMap (h : Function.Bijective (algebraMap R S)) : PreSubme
rsivePresentation R S PEmpty.{w + 1} PEmpty.{t + 1} where toPresentation
参数：h : Function.Bijective (algebraMap R S)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `algebraMap R S` is bijective, the empty generators are a pre-submersive
presentation with no relations.
-/
noncomputable def ofBijectiveAlgebraMap (h : Function.Bijective (algebraMap R S)) :
    PreSubmersivePresentation R S PEmpty.{w + 1} PEmpty.{t + 1} where
  toPresentation := Presentation.ofBijectiveAlgebraMap.{t, w} h
  map := PEmpty.elim
  map_inj (a b : PEmpty) h := by contradiction

@[simp]
/-
**Algebra.PreSubmersivePresentation.ofBijectiveAlgebraMap_jacobian** 是 Mathlib 中
的一个引理，位于命名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：ofBijectiveAlgebraMap_jacobian (h : Function.Bijective (algebraMap R S)) :
 (ofBijectiveAlgebraMap h).jacobian = 1
参数：h : Function.Bijective (algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det`：jacobian
_eq_jacobiMatrix_det : P.jacobian = algebraMap P.Ring S P.jacobiMatrix.det
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
-/
lemma ofBijectiveAlgebraMap_jacobian (h : Function.Bijective (algebraMap R S)) :
    (ofBijectiveAlgebraMap h).jacobian = 1 := by
  have : (algebraMap (ofBijectiveAlgebraMap h).Ring S).mapMatrix
      (ofBijectiveAlgebraMap h).jacobiMatrix = 1 := by
    ext (i j : PEmpty)
    contradiction
  rw [jacobian_eq_jacobiMatrix_det, RingHom.map_det, this, Matrix.det_one]

section Localization

variable (r : R) [IsLocalization.Away r S]

variable (S) in
/-- If `S` is the localization of `R` at `r`, this is the canonical submersive presentation
of `S` as `R`-algebra. -/
@[simps map]
/-
**Algebra.PreSubmersivePresentation.localizationAway** 是 Mathlib 中的一个定义，位于命名空间 `
Algebra.PreSubmersivePresentation`。
形式化陈述：localizationAway : PreSubmersivePresentation R S Unit Unit where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is the localization of `R` at `r`, this is the canonical submersive prese
ntation
of `S` as `R`-algebra.
-/
noncomputable def localizationAway : PreSubmersivePresentation R S Unit Unit where
  __ := Presentation.localizationAway S r
  map _ := ()
  map_inj _ _ h := h

@[simp]
/-
**Algebra.PreSubmersivePresentation.localizationAway_jacobiMatrix** 是 Mathlib 中的
一个引理，位于命名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：localizationAway_jacobiMatrix : (localizationAway S r).jacobiMatrix = Matr
ix.diagonal (fun () => MvPolynomial.C r)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Derivation.leibniz`：leibniz : D (a * b) = a • D b + b • D a
· 使用定理 `MvPolynomial.pderiv_X`：pderiv_X [DecidableEq σ] (i j : σ) : pderiv i (X 
j : MvPolynomial σ R) = Pi.single (M
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MvPolynomial.derivation_C`：derivation_C (D : Derivation R (MvPolynomial 
σ R) A) (a : R) : D (C a) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Derivation.map_one_eq_zero`：map_one_eq_zero : D 1 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用引理 `Algebra.PreSubmersivePresentation.jacobiMatrix_apply`：jacobiMatrix_apply
 (i j : σ) : P.jacobiMatrix i j = MvPolynomial.pderiv (P.map i) (P.relation j)
-/
lemma localizationAway_jacobiMatrix :
    (localizationAway S r).jacobiMatrix = Matrix.diagonal (fun () ↦ MvPolynomial.C r) := by
  have h : (pderiv ()) (C r * X () - 1) = C r := by simp
  ext (i : Unit) (j : Unit) : 1
  rwa [jacobiMatrix_apply]

@[simp]
/-
**Algebra.PreSubmersivePresentation.localizationAway_jacobian** 是 Mathlib 中的一个引理
，位于命名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：localizationAway_jacobian : (localizationAway S r).jacobian = algebraMap R
 S r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det`：jacobian
_eq_jacobiMatrix_det : P.jacobian = algebraMap P.Ring S P.jacobiMatrix.det
· 使用引理 `Algebra.PreSubmersivePresentation.localizationAway_jacobiMatrix`：localiz
ationAway_jacobiMatrix : (localizationAway S r).jacobiMatrix = Matrix.diagonal (
fun () => MvPolynomial.C r)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det_unique`：det_unique {n : Type*} [Unique n] [DecidableEq n] [Fi
ntype n] (A : Matrix n n R) : det A = A default default
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用引理 `Algebra.Generators.algebraMap_apply`：algebraMap_apply (x) : algebraMap P
.Ring S x = aeval (R
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma localizationAway_jacobian : (localizationAway S r).jacobian = algebraMap R S r := by
  rw [jacobian_eq_jacobiMatrix_det, localizationAway_jacobiMatrix]
  simp [show Fintype.card (localizationAway r (S := S)).rels = 1 from rfl]

end Localization

section Composition

variable {ι' σ' T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (Q : PreSubmersivePresentation S T ι' σ') (P : PreSubmersivePresentation R S ι σ)

/-- Given an `R`-algebra `S` and an `S`-algebra `T` with pre-submersive presentations,
this is the canonical pre-submersive presentation of `T` as an `R`-algebra. -/
@[simps map]
/-
**Algebra.PreSubmersivePresentation.comp** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.PreS
ubmersivePresentation`。
形式化陈述：comp : PreSubmersivePresentation R T (ι' oplus ι) (σ' oplus σ) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `R`-algebra `S` and an `S`-algebra `T` with pre-submersive presentation
s,
this is the canonical pre-submersive presentation of `T` as an `R`-algebra.
-/
noncomputable def comp : PreSubmersivePresentation R T (ι' ⊕ ι) (σ' ⊕ σ) where
  __ := Q.toPresentation.comp P.toPresentation
  map := Sum.elim (fun rq ↦ Sum.inl <| Q.map rq) (fun rp ↦ Sum.inr <| P.map rp)
  map_inj := Function.Injective.sumElim ((Sum.inl_injective).comp (Q.map_inj))
    ((Sum.inr_injective).comp (P.map_inj)) <| by simp
/-
**Algebra.PreSubmersivePresentation.toPresentation_comp** 是 Mathlib 中的一个引理，位于命名空
间 `Algebra.PreSubmersivePresentation`。
形式化陈述：toPresentation_comp : (Q.comp P).toPresentation = Q.toPresentation.comp P.
toPresentation
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toPresentation_comp : (Q.comp P).toPresentation = Q.toPresentation.comp P.toPresentation :=
  rfl
/-
**Algebra.PreSubmersivePresentation.toGenerators_comp** 是 Mathlib 中的一个引理，位于命名空间 
`Algebra.PreSubmersivePresentation`。
形式化陈述：toGenerators_comp : (Q.comp P).toGenerators = Q.toGenerators.comp P.toGene
rators
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toGenerators_comp : (Q.comp P).toGenerators = Q.toGenerators.comp P.toGenerators := rfl

/-- The dimension of the composition of two finite submersive presentations is
the sum of the dimensions. -/
/-
**Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension** 
是 Mathlib 中的一个引理，位于命名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：dimension_comp_eq_dimension_add_dimension [Finite ι] [Finite ι'] [Finite σ
] [Finite σ'] : (Q.comp P).dimension = Q.dimension + P.dimension
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.PreSubmersivePresentation.card_relations_le_card_vars_of_isFinit
e`：card_relations_le_card_vars_of_isFinite [Finite ι] : Nat.card σ <= Nat.card ι
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.card_sum`：card_sum [Finite α] [Finite β] : Nat.card (α oplus β) = Na
t.card α + Nat.card β

--- 原说明 ---
The dimension of the composition of two finite submersive presentations is
the sum of the dimensions.
-/
lemma dimension_comp_eq_dimension_add_dimension [Finite ι] [Finite ι'] [Finite σ] [Finite σ'] :
    (Q.comp P).dimension = Q.dimension + P.dimension := by
  simp only [Presentation.dimension]
  have : Nat.card σ ≤ Nat.card ι :=
    card_relations_le_card_vars_of_isFinite P
  have : Nat.card σ' ≤ Nat.card ι' :=
    card_relations_le_card_vars_of_isFinite Q
  simp only [Nat.card_sum]
  lia

section

/-!
### Jacobian of composition

Let `S` be an `R`-algebra and `T` be an `S`-algebra with presentations `P` and `Q` respectively.
In this section we compute the Jacobian of the composition of `Q` and `P` to be
the product of the Jacobians. For this we use a block decomposition of the Jacobi matrix and show
that the upper-right block vanishes, the upper-left block has determinant Jacobian of `Q` and
the lower-right block has determinant Jacobian of `P`.

-/

variable [Fintype σ] [Fintype σ']

open scoped Classical in
/-
**Algebra.PreSubmersivePresentation.jacobiMatrix_comp_inl_inr** 是 Mathlib 中的一个引理
，位于命名空间 `Algebra.PreSubmersivePresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma jacobiMatrix_comp_inl_inr (i : σ') (j : σ) :
    (Q.comp P).jacobiMatrix (Sum.inl i) (Sum.inr j) = 0 := by
  rw [jacobiMatrix_apply]
  refine MvPolynomial.pderiv_eq_zero_of_notMem_vars (fun hmem ↦ ?_)
  apply MvPolynomial.vars_rename at hmem
  simp at hmem

open scoped Classical in
/-
**Algebra.PreSubmersivePresentation.jacobiMatrix_comp_** 是 Mathlib 中的一个引理，位于命名空间
 `Algebra.PreSubmersivePresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma jacobiMatrix_comp_₁₂ : (Q.comp P).jacobiMatrix.toBlocks₁₂ = 0 := by
  ext i j : 1
  simp [Matrix.toBlocks₁₂, jacobiMatrix_comp_inl_inr]

section Q

open scoped Classical in
/-
**Algebra.PreSubmersivePresentation.jacobiMatrix_comp_inl_inl** 是 Mathlib 中的一个引理
，位于命名空间 `Algebra.PreSubmersivePresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma jacobiMatrix_comp_inl_inl (i j : σ') :
    aeval (Sum.elim X (MvPolynomial.C ∘ P.val))
      ((Q.comp P).jacobiMatrix (Sum.inl j) (Sum.inl i)) = Q.jacobiMatrix j i := by
  rw [jacobiMatrix_apply, jacobiMatrix_apply, comp_map, Sum.elim_inl,
    ← Q.comp_aeval_relation_inl P.toPresentation]
  apply aeval_sumElim_pderiv_inl

open scoped Classical in
/-
**Algebra.PreSubmersivePresentation.jacobiMatrix_comp_** 是 Mathlib 中的一个引理，位于命名空间
 `Algebra.PreSubmersivePresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma jacobiMatrix_comp_₁₁_det :
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₁₁.det = Q.jacobian := by
  rw [jacobian_eq_jacobiMatrix_det, AlgHom.map_det (aeval (Q.comp P).val), RingHom.map_det]
  congr
  ext i j : 1
  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, ← Q.jacobiMatrix_comp_inl_inl P,
    Q.algebraMap_apply]
  apply aeval_sumElim

end Q

section P

open scoped Classical in
/-
**Algebra.PreSubmersivePresentation.jacobiMatrix_comp_inr_inr** 是 Mathlib 中的一个引理
，位于命名空间 `Algebra.PreSubmersivePresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma jacobiMatrix_comp_inr_inr (i j : σ) :
    (Q.comp P).jacobiMatrix (Sum.inr i) (Sum.inr j) =
      MvPolynomial.rename Sum.inr (P.jacobiMatrix i j) := by
  rw [jacobiMatrix_apply, jacobiMatrix_apply]
  simp only [comp_map, Sum.elim_inr]
  apply pderiv_rename Sum.inr_injective

open scoped Classical in
/-
**Algebra.PreSubmersivePresentation.jacobiMatrix_comp_** 是 Mathlib 中的一个引理，位于命名空间
 `Algebra.PreSubmersivePresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma jacobiMatrix_comp_₂₂_det :
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₂₂.det = algebraMap S T P.jacobian := by
  rw [jacobian_eq_jacobiMatrix_det]
  rw [AlgHom.map_det (aeval (Q.comp P).val), RingHom.map_det, RingHom.map_det]
  congr
  ext i j : 1
  simp only [Matrix.toBlocks₂₂, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    RingHom.mapMatrix_apply, Generators.algebraMap_apply, map_aeval, coe_eval₂Hom]
  rw [jacobiMatrix_comp_inr_inr, ← IsScalarTower.algebraMap_eq]
  simp only [aeval]
  generalize P.jacobiMatrix i j = p
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [algHom_C, algebraMap_eq, eval₂_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, eval₂_mul, hp]
    simp [Presentation.toGenerators_comp, toPresentation_comp]

end P

end

/-- The Jacobian of the composition of presentations is the product of the Jacobians. -/
@[simp]
/-
**Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian** 是 
Mathlib 中的一个引理，位于命名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：comp_jacobian_eq_jacobian_smul_jacobian [Finite σ] [Finite σ'] : (Q.comp P
).jacobian = P.jacobian • Q.jacobian
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det`：jacobian
_eq_jacobiMatrix_det : P.jacobian = algebraMap P.Ring S P.jacobiMatrix.det
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.fromBlocks_toBlocks`：fromBlocks_toBlocks (M : Matrix (n oplus o) 
(l oplus m) α) : fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ 
= M
· 使用定理 `_private.Mathlib.RingTheory.Extension.Presentation.Submersive.0.Algebra.
PreSubmersivePresentation.jacobiMatrix_comp_₁₂`：∀ {R : Type u} {S : Type v} {ι :
 Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebr
a R S]   {ι' : Type u_1} {σ'…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Algebra.Generators.algebraMap_apply`：algebraMap_apply (x) : algebraMap P
.Ring S x = aeval (R
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Matrix.det_fromBlocks_zero₁₂`：det_fromBlocks_zero₁₂ (A : Matrix m m R) (
C : Matrix n m R) (D : Matrix n n R) : (Matrix.fromBlocks A 0 C D).det = A.det *
 D.det
· 使用定理 `_private.Mathlib.RingTheory.Extension.Presentation.Submersive.0.Algebra.
PreSubmersivePresentation.jacobiMatrix_comp_₁₁_det`：∀ {R : Type u} {S : Type v} 
{ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Al
gebra R S]   {ι' : Type u_1} {σ'…
· 使用定理 `_private.Mathlib.RingTheory.Extension.Presentation.Submersive.0.Algebra.
PreSubmersivePresentation.jacobiMatrix_comp_₂₂_det`：∀ {R : Type u} {S : Type v} 
{ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Al
gebra R S]   {ι' : Type u_1} {σ'…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x

--- 原说明 ---
The Jacobian of the composition of presentations is the product of the Jacobians
.
-/
lemma comp_jacobian_eq_jacobian_smul_jacobian [Finite σ] [Finite σ'] :
    (Q.comp P).jacobian = P.jacobian • Q.jacobian := by
  classical
  cases nonempty_fintype σ'
  cases nonempty_fintype σ
  rw [jacobian_eq_jacobiMatrix_det, ← Matrix.fromBlocks_toBlocks ((Q.comp P).jacobiMatrix),
    jacobiMatrix_comp_₁₂]
  convert_to
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₁₁.det *
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₂₂.det = P.jacobian • Q.jacobian
  · simp only [Generators.algebraMap_apply, ← map_mul]
    congr
    convert!
      Matrix.det_fromBlocks_zero₁₂ (Q.comp P).jacobiMatrix.toBlocks₁₁
        (Q.comp P).jacobiMatrix.toBlocks₂₁ (Q.comp P).jacobiMatrix.toBlocks₂₂
  · rw [jacobiMatrix_comp_₁₁_det, jacobiMatrix_comp_₂₂_det, mul_comm, Algebra.smul_def]

end Composition

section BaseChange

variable (T : Type*) [CommRing T] [Algebra R T] (P : PreSubmersivePresentation R S ι σ)

/-- If `P` is a pre-submersive presentation of `S` over `R` and `T` is an `R`-algebra, we
obtain a natural pre-submersive presentation of `T ⊗[R] S` over `T`. -/
/-
**Algebra.PreSubmersivePresentation.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
a.PreSubmersivePresentation`。
形式化陈述：baseChange : PreSubmersivePresentation T (T otimes[R] S) ι σ where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.PreSubmersivePresentation.map_inj`：∀ {R : Type u} {S : Type v} {
ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Alg
ebra R S]   (self : Algebra.Pre…

--- 原说明 ---
If `P` is a pre-submersive presentation of `S` over `R` and `T` is an `R`-algebr
a, we
obtain a natural pre-submersive presentation of `T ⊗[R] S` over `T`.
-/
noncomputable def baseChange : PreSubmersivePresentation T (T ⊗[R] S) ι σ where
  __ := P.toPresentation.baseChange T
  map := P.map
  map_inj := P.map_inj
/-
**Algebra.PreSubmersivePresentation.baseChange_toPresentation** 是 Mathlib 中的一个引理
，位于命名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：baseChange_toPresentation : (P.baseChange R).toPresentation = P.toPresenta
tion.baseChange R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma baseChange_toPresentation :
    (P.baseChange R).toPresentation = P.toPresentation.baseChange R :=
  rfl
/-
**Algebra.PreSubmersivePresentation.baseChange_ring** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebra.PreSubmersivePresentation`。
形式化陈述：baseChange_ring : (P.baseChange R).Ring = P.Ring
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma baseChange_ring : (P.baseChange R).Ring = P.Ring := rfl

@[simp]
/-
**Algebra.PreSubmersivePresentation.baseChange_jacobian** 是 Mathlib 中的一个引理，位于命名空
间 `Algebra.PreSubmersivePresentation`。
形式化陈述：baseChange_jacobian [Finite σ] : (P.baseChange T).jacobian = 1 otimesₜ P.j
acobian
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det`：jacobian
_eq_jacobiMatrix_det : P.jacobian = algebraMap P.Ring S P.jacobiMatrix.det
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.PreSubmersivePresentation.map_inj`：∀ {R : Type u} {S : Type v} {
ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Alg
ebra R S]   (self : Algebra.Pre…
· 使用引理 `Algebra.PreSubmersivePresentation.jacobiMatrix_apply`：jacobiMatrix_apply
 (i j : σ) : P.jacobiMatrix i j = MvPolynomial.pderiv (P.map i) (P.relation j)
· 使用定理 `Algebra.Presentation.baseChange_relation`：∀ {R : Type u} {S : Type v} {ι
 : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Alge
bra R S]   (T : Type u_1) [ins…
· 使用定理 `MvPolynomial.pderiv_map`：pderiv_map {S} [CommSemiring S] {φ : R ->+* S} 
{f : MvPolynomial σ R} {i : σ} : pderiv i (map φ f) = map φ (pderiv i f)
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用引理 `Algebra.Generators.algebraMap_apply`：algebraMap_apply (x) : algebraMap P
.Ring S x = aeval (R
· 使用定理 `MvPolynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : σ -> B) (p 
: MvPolynomial σ R) : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MvPolynomial.aeval_one_tmul`：aeval_one_tmul (f : σ -> S) (p : MvPolynomi
al σ R) : (aeval fun x => (1 otimesₜ[R] f x : N otimes[R] S)) p = 1 otimesₜ[R] (
aeval f) p
-/
lemma baseChange_jacobian [Finite σ] : (P.baseChange T).jacobian = 1 ⊗ₜ P.jacobian := by
  classical
  cases nonempty_fintype σ
  simp_rw [jacobian_eq_jacobiMatrix_det]
  have h : (baseChange T P).jacobiMatrix =
      (MvPolynomial.map (algebraMap R T)).mapMatrix P.jacobiMatrix := by
    ext i j : 1
    simp only [baseChange, jacobiMatrix_apply, Presentation.baseChange_relation,
      RingHom.mapMatrix_apply, Matrix.map_apply,
      Presentation.baseChange_toGenerators, MvPolynomial.pderiv_map]
  rw [h, ← RingHom.map_det, Generators.algebraMap_apply, aeval_map_algebraMap, P.algebraMap_apply]
  apply aeval_one_tmul

end BaseChange

/-- Given a pre-submersive presentation `P` and equivalences `ι' ≃ ι` and
`σ' ≃ σ`, this is the induced pre-submersive presentation with variables indexed
by `ι` and relations indexed by `κ`. -/
@[simps toPresentation, simps -isSimp map]
/-
**Algebra.PreSubmersivePresentation.reindex** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.P
reSubmersivePresentation`。
形式化陈述：reindex (P : PreSubmersivePresentation R S ι σ) {ι' σ' : Type*} (e : ι' ≃ 
ι) (f : σ' ≃ σ) : PreSubmersivePresentation R S ι' σ' where __
参数：P : PreSubmersivePresentation R S ι σ；e : ι' ≃ ι；f : σ' ≃ σ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a pre-submersive presentation `P` and equivalences `ι' ≃ ι` and
`σ' ≃ σ`, this is the induced pre-submersive presentation with variables indexed
by `ι` and relations indexed by `κ`.
-/
noncomputable def reindex (P : PreSubmersivePresentation R S ι σ)
    {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ) :
    PreSubmersivePresentation R S ι' σ' where
  __ := P.toPresentation.reindex e f
  map := e.symm ∘ P.map ∘ f
  map_inj := by
    rw [Function.Injective.of_comp_iff e.symm.injective, Function.Injective.of_comp_iff P.map_inj]
    exact f.injective
/-
**Algebra.PreSubmersivePresentation.jacobiMatrix_reindex** 是 Mathlib 中的一个引理，位于命名
空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：jacobiMatrix_reindex {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ) [Fintype σ'
] [DecidableEq σ'] [Fintype σ] [DecidableEq σ] : (P.reindex e f).jacobiMatrix = 
(P.jacobiMatrix.reindex f.symm f.symm).map (MvPolynomial.rename e.symm)
参数：e : ι' ≃ ι；f : σ' ≃ σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.PreSubmersivePresentation.jacobiMatrix_apply`：jacobiMatrix_apply
 (i j : σ) : P.jacobiMatrix i j = MvPolynomial.pderiv (P.map i) (P.relation j)
· 使用引理 `MvPolynomial.pderiv_rename`：pderiv_rename {τ : Type*} {f : σ -> τ} (hf :
 Function.Injective f) (x : σ) (p : MvPolynomial σ R) : pderiv (f x) (rename f p
) = rename f (pd…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma jacobiMatrix_reindex {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ)
    [Fintype σ'] [DecidableEq σ'] [Fintype σ] [DecidableEq σ] :
    (P.reindex e f).jacobiMatrix =
      (P.jacobiMatrix.reindex f.symm f.symm).map (MvPolynomial.rename e.symm) := by
  ext i j : 1
  simp [jacobiMatrix_apply,
    MvPolynomial.pderiv_rename e.symm.injective, reindex, Presentation.reindex]

@[simp]
/-
**Algebra.PreSubmersivePresentation.jacobian_reindex** 是 Mathlib 中的一个引理，位于命名空间 `
Algebra.PreSubmersivePresentation`。
形式化陈述：jacobian_reindex (P : PreSubmersivePresentation R S ι σ) {ι' σ' : Type*} (
e : ι' ≃ ι) (f : σ' ≃ σ) [Finite σ] [Finite σ'] : (P.reindex e f).jacobian = P.j
acobian
参数：P : PreSubmersivePresentation R S ι σ；e : ι' ≃ ι；f : σ' ≃ σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det`：jacobian
_eq_jacobiMatrix_det : P.jacobian = algebraMap P.Ring S P.jacobiMatrix.det
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用引理 `Algebra.PreSubmersivePresentation.jacobiMatrix_reindex`：jacobiMatrix_rei
ndex {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ) [Fintype σ'] [DecidableEq σ'] [Fi
ntype σ] [DecidableEq σ] : (P.reindex e f).j…
· 使用引理 `Algebra.Generators.algebraMap_apply`：algebraMap_apply (x) : algebraMap P
.Ring S x = aeval (R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.PreSubmersivePresentation.reindex_toPresentation`：∀ {R : Type u}
 {S : Type v} {ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S
] [inst_2 : Algebra R S]   (P : Algebra.PreSub…
· 使用定理 `Algebra.Presentation.reindex_toGenerators`：∀ {R : Type u} {S : Type v} {
ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Alg
ebra R S]   (P : Algebra.Presen…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_submatrix_equiv_self`：det_submatrix_equiv_self (e : n ≃ m) (A
 : Matrix m m R) : det (A.submatrix e e) = det A
· 使用定理 `AlgHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Fintyp
e n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] [in
st_4…
· 使用定理 `AlgHom.mapMatrix_apply`：∀ {m : Type u_2} {R : Type u_7} {α : Type u_11} 
{β : Type u_12} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : CommSemi
ring R] [ins…
· 使用定理 `Matrix.map_map`：map_map {M : Matrix m n α} {β γ : Type*} {f : α -> β} {g
 : β -> γ} : (M.map f).map g = M.map (g ∘ f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `MvPolynomial.rename_comp_rename`：rename_comp_rename (f : σ -> τ) (g : τ 
-> α) : (rename (R
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `MvPolynomial.rename_id`：rename_id : rename id = AlgHom.id R (MvPolynomia
l σ R)
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma jacobian_reindex (P : PreSubmersivePresentation R S ι σ)
    {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ) [Finite σ] [Finite σ'] :
    (P.reindex e f).jacobian = P.jacobian := by
  classical
  cases nonempty_fintype σ
  cases nonempty_fintype σ'
  simp_rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  simp only [reindex_toPresentation, Presentation.reindex_toGenerators, jacobiMatrix_reindex,
    Matrix.reindex_apply, Equiv.symm_symm, Generators.algebraMap_apply, Generators.reindex_val]
  simp_rw [← MvPolynomial.aeval_rename,
    ← AlgHom.mapMatrix_apply, ← Matrix.det_submatrix_equiv_self f, AlgHom.map_det,
    AlgHom.mapMatrix_apply, Matrix.map_map]
  simp [← AlgHom.coe_comp, rename_comp_rename, rename_id]

section

variable {v : ι → MvPolynomial σ R} (a : ι → σ) (ha : Function.Injective a)
  (s : MvPolynomial σ R ⧸ (Ideal.span <| Set.range v) → MvPolynomial σ R)
  (hs : ∀ x, Ideal.Quotient.mk _ (s x) = x)

/--
The naive pre-submersive presentation of a quotient `R[Xᵢ] ⧸ (vⱼ)`.
If the definitional equality of the section matters, it can be explicitly provided.

To construct the associated submersive presentation, use
`PreSubmersivePresentation.jacobiMatrix_naive`.
-/
@[simps! toPresentation]
noncomputable
/-
**Algebra.PreSubmersivePresentation.naive** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Pre
SubmersivePresentation`。
形式化陈述：naive {v : ι -> MvPolynomial σ R} (a : ι -> σ) (ha : Function.Injective a)
 (s : MvPolynomial σ R ⧸ (Ideal.span <| Set.range v) -> MvPolynomial σ R
参数：a : ι -> σ；ha : Function.Injective a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def naive {v : ι → MvPolynomial σ R} (a : ι → σ) (ha : Function.Injective a)
    (s : MvPolynomial σ R ⧸ (Ideal.span <| Set.range v) → MvPolynomial σ R :=
      Function.surjInv Ideal.Quotient.mk_surjective)
    (hs : ∀ x, Ideal.Quotient.mk _ (s x) = x := by apply Function.surjInv_eq) :
    PreSubmersivePresentation R (MvPolynomial σ R ⧸ (Ideal.span <| Set.range v)) σ ι where
  __ := Presentation.naive s hs
  map := a
  map_inj := ha
/-
**Algebra.PreSubmersivePresentation.jacobiMatrix_naive** 是 Mathlib 中的一个定理，位于命名空间
 `Algebra.PreSubmersivePresentation`。
形式化陈述：∀ {R : Type u} {ι : Type w} {σ : Type t} [inst : CommRing R] {v : ι → MvPo
lynomial σ R} (a : ι → σ)   (ha : Function.Injective a) (s : MvPolynomial σ R ⧸ 
Ideal.span (Set.range v) → MvPolynomial σ R)   (hs : ∀ (x : MvPolynomial σ R ⧸ I
deal.span (Set.range v)), (Ideal.Quotient.mk (Ideal.span (Set.range v))) (s x) =
 x)   [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (i j : ι),   (Algebra.PreSub
mersivePresentation.naive a ha s hs).jacobiMatrix i j = (MvPolynomial.pderiv (a 
i)) (v j)
参数：a : ι → σ；ha : Function.Injective a；s : MvPolynomial σ R ⧸ Ideal.span (Set.ra
nge v) → MvPolynomial σ R；hs : ∀ (x : MvPolynomial σ R ⧸ Ideal.span (Set.range v
)), (Ideal.Quotient.mk (Ideal.span (Set.range v))) (s x) = x；i j : ι；Algebra.Pre
SubmersivePresentation.naive a ha s hs；MvPolynomial.pderiv (a i)；v j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `Algebra.PreSubmersivePresentation.jacobiMatrix_apply`：jacobiMatrix_apply
 (i j : σ) : P.jacobiMatrix i j = MvPolynomial.pderiv (P.map i) (P.relation j)
-/
@[simp] lemma jacobiMatrix_naive [Fintype ι] [DecidableEq ι] (i j : ι) :
    (naive a ha s hs).jacobiMatrix i j = (v j).pderiv (a i) :=
  jacobiMatrix_apply _ _ _

end

end Constructions

end PreSubmersivePresentation

variable [Finite σ]

/--
A `PreSubmersivePresentation` is submersive if its Jacobian is a unit in `S`
and the presentation is finite.
-/
/-
**Algebra.SubmersivePresentation** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u) →   (S : Type v) →     Type w →       (σ : Type t) →         
[inst : CommRing R] → [inst_1 : CommRing S] → [Algebra R S] → [Finite σ] → Type 
(max (max (max t u) v) w)
参数：max (max t u) v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `PreSubmersivePresentation` is submersive if its Jacobian is a unit in `S`
and the presentation is finite.
-/
structure SubmersivePresentation extends PreSubmersivePresentation.{t, w} R S ι σ where
  jacobian_isUnit : IsUnit toPreSubmersivePresentation.jacobian

namespace SubmersivePresentation

open PreSubmersivePresentation

section Constructions

variable {R S ι σ} in
/-- Transport a submersive presentation along an algebra isomorphism. -/
@[simps toPreSubmersivePresentation]
/-
**Algebra.SubmersivePresentation.ofAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.S
ubmersivePresentation`。
形式化陈述：ofAlgEquiv (P : SubmersivePresentation R S ι σ) {T : Type*} [CommRing T] [
Algebra R T] (e : S ≃ₐ[R] T) : SubmersivePresentation R T ι σ where __
参数：P : SubmersivePresentation R S ι σ；e : S ≃ₐ[R] T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport a submersive presentation along an algebra isomorphism.
-/
noncomputable def ofAlgEquiv
    (P : SubmersivePresentation R S ι σ) {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T) :
    SubmersivePresentation R T ι σ where
  __ := P.toPreSubmersivePresentation.ofAlgEquiv e
  jacobian_isUnit := by simp [P.jacobian_isUnit]

variable {R S} in
/-- If `algebraMap R S` is bijective, the empty generators are a submersive
presentation with no relations. -/
/-
**Algebra.SubmersivePresentation.ofBijectiveAlgebraMap** 是 Mathlib 中的一个定义，位于命名空间
 `Algebra.SubmersivePresentation`。
形式化陈述：ofBijectiveAlgebraMap (h : Function.Bijective (algebraMap R S)) : Submersi
vePresentation R S PEmpty.{w + 1} PEmpty.{t + 1} where __
参数：h : Function.Bijective (algebraMap R S)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `algebraMap R S` is bijective, the empty generators are a submersive
presentation with no relations.
-/
noncomputable def ofBijectiveAlgebraMap (h : Function.Bijective (algebraMap R S)) :
    SubmersivePresentation R S PEmpty.{w + 1} PEmpty.{t + 1} where
  __ := PreSubmersivePresentation.ofBijectiveAlgebraMap.{t, w} h
  jacobian_isUnit := by
    rw [ofBijectiveAlgebraMap_jacobian]
    exact isUnit_one

/-- The canonical submersive `R`-presentation of `R` with no generators and no relations. -/
/-
**Algebra.SubmersivePresentation.id** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Submersiv
ePresentation`。
形式化陈述：id : SubmersivePresentation R R PEmpty.{w + 1} PEmpty.{t + 1}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)

--- 原说明 ---
The canonical submersive `R`-presentation of `R` with no generators and no relat
ions.
-/
noncomputable def id : SubmersivePresentation R R PEmpty.{w + 1} PEmpty.{t + 1} :=
  ofBijectiveAlgebraMap Function.bijective_id

section Composition
variable {R S ι σ}
variable {T ι' σ' : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [Finite σ'] (Q : SubmersivePresentation S T ι' σ') (P : SubmersivePresentation R S ι σ)

/-- Given an `R`-algebra `S` and an `S`-algebra `T` with submersive presentations,
this is the canonical submersive presentation of `T` as an `R`-algebra. -/
/-
**Algebra.SubmersivePresentation.comp** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Submers
ivePresentation`。
形式化陈述：comp : SubmersivePresentation R T (ι' oplus ι) (σ' oplus σ) where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)

--- 原说明 ---
Given an `R`-algebra `S` and an `S`-algebra `T` with submersive presentations,
this is the canonical submersive presentation of `T` as an `R`-algebra.
-/
noncomputable def comp : SubmersivePresentation R T (ι' ⊕ ι) (σ' ⊕ σ) where
  __ := Q.toPreSubmersivePresentation.comp P.toPreSubmersivePresentation
  jacobian_isUnit := by
    rw [comp_jacobian_eq_jacobian_smul_jacobian, Algebra.smul_def, IsUnit.mul_iff]
    exact ⟨RingHom.isUnit_map _ <| P.jacobian_isUnit, Q.jacobian_isUnit⟩

end Composition

section Localization

variable {R} (r : R) [IsLocalization.Away r S]

/-- If `S` is the localization of `R` at `r`, this is the canonical submersive presentation
of `S` as `R`-algebra. -/
/-
**Algebra.SubmersivePresentation.localizationAway** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebra.SubmersivePresentation`。
形式化陈述：localizationAway : SubmersivePresentation R S Unit Unit where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `S` is the localization of `R` at `r`, this is the canonical submersive prese
ntation
of `S` as `R`-algebra.
-/
noncomputable def localizationAway : SubmersivePresentation R S Unit Unit where
  __ := PreSubmersivePresentation.localizationAway S r
  jacobian_isUnit := by
    rw [localizationAway_jacobian]
    exact IsLocalization.map_units _ (⟨r, 1, by simp⟩ : Submonoid.powers r)

end Localization

section BaseChange

variable (T) [CommRing T] [Algebra R T] (P : SubmersivePresentation R S ι σ)

variable {R S ι σ} in
/-- If `P` is a submersive presentation of `S` over `R` and `T` is an `R`-algebra, we
obtain a natural submersive presentation of `T ⊗[R] S` over `T`. -/
/-
**Algebra.SubmersivePresentation.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.S
ubmersivePresentation`。
形式化陈述：baseChange : SubmersivePresentation T (T otimes[R] S) ι σ where toPreSubme
rsivePresentation
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is a submersive presentation of `S` over `R` and `T` is an `R`-algebra, w
e
obtain a natural submersive presentation of `T ⊗[R] S` over `T`.
-/
noncomputable def baseChange : SubmersivePresentation T (T ⊗[R] S) ι σ where
  toPreSubmersivePresentation := P.toPreSubmersivePresentation.baseChange T
  jacobian_isUnit :=
    P.baseChange_jacobian T ▸ P.jacobian_isUnit.map TensorProduct.includeRight

end BaseChange

variable {R S ι σ} in
/-- Given a submersive presentation `P` and equivalences `ι' ≃ ι` and
`σ' ≃ σ`, this is the induced submersive presentation with variables indexed
by `ι'` and relations indexed by `σ'` -/
@[simps toPreSubmersivePresentation]
/-
**Algebra.SubmersivePresentation.reindex** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Subm
ersivePresentation`。
形式化陈述：reindex (P : SubmersivePresentation R S ι σ) {ι' σ' : Type*} [Finite σ'] (
e : ι' ≃ ι) (f : σ' ≃ σ) : SubmersivePresentation R S ι' σ' where __
参数：P : SubmersivePresentation R S ι σ；e : ι' ≃ ι；f : σ' ≃ σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a submersive presentation `P` and equivalences `ι' ≃ ι` and
`σ' ≃ σ`, this is the induced submersive presentation with variables indexed
by `ι'` and relations indexed by `σ'`
-/
noncomputable def reindex (P : SubmersivePresentation R S ι σ)
    {ι' σ' : Type*} [Finite σ'] (e : ι' ≃ ι) (f : σ' ≃ σ) : SubmersivePresentation R S ι' σ' where
  __ := P.toPreSubmersivePresentation.reindex e f
  jacobian_isUnit := by simp [P.jacobian_isUnit]

set_option backward.isDefEq.respectTransparency false in
/-- If `S = 0`, this is the submersive presentation on one generator and one relation. -/
@[simps]
/-
**Algebra.SubmersivePresentation.ofSubsingleton** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
ra.SubmersivePresentation`。
形式化陈述：ofSubsingleton [Subsingleton S] : SubmersivePresentation R S PUnit PUnit w
here val _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `S = 0`, this is the submersive presentation on one generator and one relatio
n.
-/
noncomputable def ofSubsingleton [Subsingleton S] : SubmersivePresentation R S PUnit PUnit where
  val _ := 1
  σ' _ := 1
  aeval_val_σ' _ := Subsingleton.elim _ _
  relation _ := 1
  span_range_relation_eq_ker := by
    simp [Generators.ker, Extension.ker, RingHom.ker_eq_top_of_subsingleton]
  map _ := ⟨⟩
  map_inj _ _ _ := rfl
  jacobian_isUnit := isUnit_of_subsingleton _

end Constructions

variable {R S ι σ}

open scoped Classical in
/-- If `P` is submersive, `PreSubmersivePresentation.aevalDifferential` is an isomorphism. -/
/-
**Algebra.SubmersivePresentation.aevalDifferentialEquiv** 是 Mathlib 中的一个定义，位于命名空
间 `Algebra.SubmersivePresentation`。
形式化陈述：aevalDifferentialEquiv (P : SubmersivePresentation R S ι σ) : (σ -> S) ≃ₗ[
S] (σ -> S)
参数：P : SubmersivePresentation R S ι σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is submersive, `PreSubmersivePresentation.aevalDifferential` is an isomor
phism.
-/
noncomputable def aevalDifferentialEquiv (P : SubmersivePresentation R S ι σ) :
    (σ → S) ≃ₗ[S] (σ → S) :=
  haveI : Fintype σ := Fintype.ofFinite σ
  have :
      IsUnit (LinearMap.toMatrix (Pi.basisFun S σ) (Pi.basisFun S σ) P.aevalDifferential).det := by
    convert! P.jacobian_isUnit
    rw [LinearMap.toMatrix_eq_toMatrix', jacobian_eq_jacobiMatrix_det,
      aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix, P.algebraMap_eq]
    simp [RingHom.map_det]
  LinearEquiv.ofIsUnitDet this

variable (P : SubmersivePresentation R S ι σ)

@[simp]
/-
**Algebra.SubmersivePresentation.aevalDifferentialEquiv_apply** 是 Mathlib 中的一个引理
，位于命名空间 `Algebra.SubmersivePresentation`。
形式化陈述：aevalDifferentialEquiv_apply (x : σ -> S) : P.aevalDifferentialEquiv x = P
.aevalDifferential x
参数：x : σ -> S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma aevalDifferentialEquiv_apply (x : σ → S) :
    P.aevalDifferentialEquiv x = P.aevalDifferential x :=
  rfl

/-- If `P` is a submersive presentation, the partial derivatives of `P.relation i` by
`P.map j` form a basis of `σ → S`. -/
/-
**Algebra.SubmersivePresentation.basisDeriv** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.S
ubmersivePresentation`。
形式化陈述：basisDeriv (P : SubmersivePresentation R S ι σ) : Basis σ S (σ -> S)
参数：P : SubmersivePresentation R S ι σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is a submersive presentation, the partial derivatives of `P.relation i` b
y
`P.map j` form a basis of `σ → S`.
-/
noncomputable def basisDeriv (P : SubmersivePresentation R S ι σ) : Basis σ S (σ → S) :=
  Basis.map (Pi.basisFun S σ) P.aevalDifferentialEquiv

@[simp]
/-
**Algebra.SubmersivePresentation.basisDeriv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebra.SubmersivePresentation`。
形式化陈述：basisDeriv_apply (i j : σ) : P.basisDeriv i j = (aeval P.val) (pderiv (P.m
ap j) (P.relation i))
参数：i j : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.basisFun_apply`：basisFun_apply [DecidableEq η] (i) : basisFun R η i =
 Pi.single i 1
· 使用引理 `Algebra.PreSubmersivePresentation.aevalDifferential_single`：aevalDiffere
ntial_single [DecidableEq σ] (i j : σ) : P.aevalDifferential (Pi.single i 1) j =
 aeval P.val (pderiv (P.map j) (P.relation i))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma basisDeriv_apply (i j : σ) :
    P.basisDeriv i j = (aeval P.val) (pderiv (P.map j) (P.relation i)) := by
  classical
  simp [basisDeriv]
/-
**Algebra.SubmersivePresentation.linearIndependent_aeval_val_pderiv_relation** 是
 Mathlib 中的一个引理，位于命名空间 `Algebra.SubmersivePresentation`。
形式化陈述：linearIndependent_aeval_val_pderiv_relation : LinearIndependent S (fun i j
 => (aeval P.val) (pderiv (P.map j) (P.relation i)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
-/
lemma linearIndependent_aeval_val_pderiv_relation :
    LinearIndependent S (fun i j ↦ (aeval P.val) (pderiv (P.map j) (P.relation i))) := by
  simp_rw [← SubmersivePresentation.basisDeriv_apply]
  exact P.basisDeriv.linearIndependent

end SubmersivePresentation

end Algebra

