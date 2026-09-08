/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Other constructions isomorphic to Clifford Algebras

This file contains isomorphisms showing that other types are equivalent to some `CliffordAlgebra`.

## Rings

* `CliffordAlgebraRing.equiv`: any ring is equivalent to a `CliffordAlgebra` over a
  zero-dimensional vector space.

## Complex numbers

* `CliffordAlgebraComplex.equiv`: the `Complex` numbers are equivalent as an `ℝ`-algebra to a
  `CliffordAlgebra` over a one-dimensional vector space with a quadratic form that satisfies
  `Q (ι Q 1) = -1`.
* `CliffordAlgebraComplex.toComplex`: the forward direction of this equiv
* `CliffordAlgebraComplex.ofComplex`: the reverse direction of this equiv

We show additionally that this equivalence sends `Complex.conj` to `CliffordAlgebra.involute` and
vice-versa:

* `CliffordAlgebraComplex.toComplex_involute`
* `CliffordAlgebraComplex.ofComplex_conj`

Note that in this algebra `CliffordAlgebra.reverse` is the identity and so the clifford conjugate
is the same as `CliffordAlgebra.involute`.

## Quaternion algebras

* `CliffordAlgebraQuaternion.equiv`: a `QuaternionAlgebra` over `R` is equivalent as an
  `R`-algebra to a clifford algebra over `R × R`, sending `i` to `(0, 1)` and `j` to `(1, 0)`.
* `CliffordAlgebraQuaternion.toQuaternion`: the forward direction of this equiv
* `CliffordAlgebraQuaternion.ofQuaternion`: the reverse direction of this equiv

We show additionally that this equivalence sends `QuaternionAlgebra.conj` to the clifford conjugate
and vice-versa:

* `CliffordAlgebraQuaternion.toQuaternion_star`
* `CliffordAlgebraQuaternion.ofQuaternion_star`

## Dual numbers

* `CliffordAlgebraDualNumber.equiv`: `R[ε]` is equivalent as an `R`-algebra to a clifford
  algebra over `R` where `Q = 0`.

-/

@[expose] public section


open CliffordAlgebra

/-! ### The clifford algebra isomorphic to a ring -/


namespace CliffordAlgebraRing

open scoped ComplexConjugate

variable {R : Type*} [CommRing R]

@[simp]
/-
**CliffordAlgebraRing.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebraRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_eq_zero : ι (0 : QuadraticForm R Unit) = 0 :=
  Subsingleton.elim _ _

/-- Since the vector space is empty the ring is commutative. -/
/-
**CliffordAlgebraRing.** 是 Mathlib 中的一个实例，位于命名空间 `CliffordAlgebraRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Since the vector space is empty the ring is commutative.
-/
instance : CommRing (CliffordAlgebra (0 : QuadraticForm R Unit)) where
  mul_comm := fun x y => by
    induction x using CliffordAlgebra.induction with
    | algebraMap r => apply Algebra.commutes
    | ι x => simp
    | add x₁ x₂ hx₁ hx₂ => rw [mul_add, add_mul, hx₁, hx₂]
    | mul x₁ x₂ hx₁ hx₂ => rw [mul_assoc, hx₂, ← mul_assoc, hx₁, ← mul_assoc]
/-
**CliffordAlgebraRing.reverse_apply** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebraRi
ng`。
形式化陈述：reverse_apply (x : CliffordAlgebra (0 : QuadraticForm R Unit)) : x.reverse
 = x
参数：x : CliffordAlgebra (0 : QuadraticForm R Unit)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.induction`：induction {C : CliffordAlgebra Q -> Prop} (al
gebraMap : forall r, C (algebraMap R (CliffordAlgebra Q) r)) (ι : forall x, C (ι
 Q x)) (mul : f…
· 使用定理 `CliffordAlgebra.reverse.commutes`：∀ {R : Type u_1} [inst : CommRing R] {
M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Quad
raticForm R M} (r : R)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebraRing.ι_eq_zero`：ι_eq_zero : ι (0 : QuadraticForm R Unit) 
= 0
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `CliffordAlgebra.reverse.map_mul`：∀ {R : Type u_1} [inst : CommRing R] {M
 : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Quadr
aticForm R M} (a b : …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
-/
theorem reverse_apply (x : CliffordAlgebra (0 : QuadraticForm R Unit)) :
    x.reverse = x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact reverse.commutes _
  | ι x => rw [ι_eq_zero, LinearMap.zero_apply, reverse.map_zero]
  | mul x₁ x₂ hx₁ hx₂ => rw [reverse.map_mul, mul_comm, hx₁, hx₂]
  | add x₁ x₂ hx₁ hx₂ => rw [reverse.map_add, hx₁, hx₂]

@[simp]
/-
**CliffordAlgebraRing.reverse_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebraRi
ng`。
形式化陈述：reverse_eq_id : (reverse : CliffordAlgebra (0 : QuadraticForm R Unit) ->ₗ[
R] _) = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `CliffordAlgebraRing.reverse_apply`：reverse_apply (x : CliffordAlgebra (0
 : QuadraticForm R Unit)) : x.reverse = x
-/
theorem reverse_eq_id :
    (reverse : CliffordAlgebra (0 : QuadraticForm R Unit) →ₗ[R] _) = LinearMap.id :=
  LinearMap.ext reverse_apply

@[simp]
/-
**CliffordAlgebraRing.involute_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebraR
ing`。
形式化陈述：involute_eq_id : (involute : CliffordAlgebra (0 : QuadraticForm R Unit) ->
ₐ[R] _) = AlgHom.id R _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] 
{f g : CliffordAlgebra Q ->ₐ[R] A} : f.toLinearMap.comp (ι Q) = g.toLinearMap.co
mp (ι Q) -> f…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `CliffordAlgebraRing.ι_eq_zero`：ι_eq_zero : ι (0 : QuadraticForm R Unit) 
= 0
· 使用定理 `LinearMap.comp_zero`：comp_zero (g : M₂ ->ₛₗ[σ₂₃] M₃) : (g.comp (0 : M ->
ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁₃] M₃) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem involute_eq_id :
    (involute : CliffordAlgebra (0 : QuadraticForm R Unit) →ₐ[R] _) = AlgHom.id R _ := by ext; simp

/-- The clifford algebra over a 0-dimensional vector space is isomorphic to its scalars. -/
/-
**CliffordAlgebraRing.equiv** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebraRing`。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → CliffordAlgebra 0 ≃ₐ[R] R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The clifford algebra over a 0-dimensional vector space is isomorphic to its scal
ars.
-/
protected def equiv : CliffordAlgebra (0 : QuadraticForm R Unit) ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom
    (CliffordAlgebra.lift (0 : QuadraticForm R Unit) <|
      ⟨0, fun _ : Unit => (zero_mul (0 : R)).trans (algebraMap R _).map_zero.symm⟩)
    (Algebra.ofId R _) (by ext)
    (by ext : 1; rw [ι_eq_zero, LinearMap.comp_zero, LinearMap.comp_zero])

end CliffordAlgebraRing

/-! ### The clifford algebra isomorphic to the complex numbers -/


namespace CliffordAlgebraComplex

open scoped ComplexConjugate

/-- The quadratic form sending elements to the negation of their square. -/
/-
**CliffordAlgebraComplex.Q** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebraComplex`。
形式化陈述：Q : QuadraticForm Real Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quadratic form sending elements to the negation of their square.
-/
def Q : QuadraticForm ℝ ℝ :=
  -QuadraticMap.sq

@[simp]
/-
**CliffordAlgebraComplex.Q_apply** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebraCompl
ex`。
形式化陈述：Q_apply (r : Real) : Q r = -(r * r)
参数：r : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Q_apply (r : ℝ) : Q r = -(r * r) :=
  rfl

/-- Intermediate result for `CliffordAlgebraComplex.equiv`: clifford algebras over
`CliffordAlgebraComplex.Q` above can be converted to `ℂ`. -/
/-
**CliffordAlgebraComplex.toComplex** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebraCom
plex`。
形式化陈述：toComplex : CliffordAlgebra Q ->ₐ[Real] Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Intermediate result for `CliffordAlgebraComplex.equiv`: clifford algebras over
`CliffordAlgebraComplex.Q` above can be converted to `ℂ`.
-/
def toComplex : CliffordAlgebra Q →ₐ[ℝ] ℂ :=
  CliffordAlgebra.lift Q
    ⟨LinearMap.toSpanSingleton _ _ Complex.I, fun r => by
      dsimp [LinearMap.toSpanSingleton, LinearMap.id]
      rw [mul_mul_mul_comm]
      simp⟩

@[simp]
/-
**CliffordAlgebraComplex.toComplex_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebraCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toComplex_ι (r : ℝ) : toComplex (ι Q r) = r • Complex.I :=
  CliffordAlgebra.lift_ι_apply _ _ r

/-- `CliffordAlgebra.involute` is analogous to `Complex.conj`. -/
@[simp]
/-
**CliffordAlgebraComplex.toComplex_involute** 是 Mathlib 中的一个定理，位于命名空间 `CliffordA
lgebraComplex`。
形式化陈述：toComplex_involute (c : CliffordAlgebra Q) : toComplex (involute c) = conj
 (toComplex c)
参数：c : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.involute_ι`：involute_ι (m : M) : involute (ι Q m) = -ι Q
 m
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `CliffordAlgebraComplex.toComplex_ι`：toComplex_ι (r : Real) : toComplex (
ι Q r) = r • Complex.I
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CliffordAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] 
{f g : CliffordAlgebra Q ->ₐ[R] A} : f.toLinearMap.comp (ι Q) = g.toLinearMap.co
mp (ι Q) -> f…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…

--- 原说明 ---
`CliffordAlgebra.involute` is analogous to `Complex.conj`.
-/
theorem toComplex_involute (c : CliffordAlgebra Q) :
    toComplex (involute c) = conj (toComplex c) := by
  have : toComplex (involute (ι Q 1)) = conj (toComplex (ι Q 1)) := by
    simp only [involute_ι, toComplex_ι, map_neg, one_smul, Complex.conj_I]
  suffices toComplex.comp involute = Complex.conjAe.toAlgHom.comp toComplex by
    exact AlgHom.congr_fun this c
  ext : 2
  exact this

/-- Intermediate result for `CliffordAlgebraComplex.equiv`: `ℂ` can be converted to
`CliffordAlgebraComplex.Q` above can be converted to. -/
/-
**CliffordAlgebraComplex.ofComplex** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebraCom
plex`。
形式化陈述：ofComplex : Complex ->ₐ[Real] CliffordAlgebra Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Intermediate result for `CliffordAlgebraComplex.equiv`: `ℂ` can be converted to
`CliffordAlgebraComplex.Q` above can be converted to.
-/
def ofComplex : ℂ →ₐ[ℝ] CliffordAlgebra Q :=
  Complex.lift
    ⟨CliffordAlgebra.ι Q 1, by
      rw [CliffordAlgebra.ι_sq_scalar, Q_apply, one_mul, map_neg, map_one]⟩

@[simp]
/-
**CliffordAlgebraComplex.ofComplex_I** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebraC
omplex`。
形式化陈述：ofComplex_I : ofComplex Complex.I = ι Q 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.liftAux_apply_I`：liftAux_apply_I (I' : A) (hI') : liftAux I' hI'
 I = I'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.ι_sq_scalar`：ι_sq_scalar (m : M) : ι Q m * ι Q m = algeb
raMap R _ (Q m)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
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
-/
theorem ofComplex_I : ofComplex Complex.I = ι Q 1 :=
  Complex.liftAux_apply_I _ (by simp)

@[simp]
/-
**CliffordAlgebraComplex.toComplex_comp_ofComplex** 是 Mathlib 中的一个定理，位于命名空间 `Cli
ffordAlgebraComplex`。
形式化陈述：toComplex_comp_ofComplex : toComplex.comp ofComplex = AlgHom.id Real Compl
ex
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.algHom_ext`：algHom_ext ⦃f g : Complex ->ₐ[Real] A⦄ (h : f I = g 
I) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebraComplex.ofComplex_I`：ofComplex_I : ofComplex Complex.I = 
ι Q 1
· 使用定理 `CliffordAlgebraComplex.toComplex_ι`：toComplex_ι (r : Real) : toComplex (
ι Q r) = r • Complex.I
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem toComplex_comp_ofComplex : toComplex.comp ofComplex = AlgHom.id ℝ ℂ := by
  ext1
  dsimp only [AlgHom.comp_apply, Subtype.coe_mk, AlgHom.id_apply]
  rw [ofComplex_I, toComplex_ι, one_smul]

@[simp]
/-
**CliffordAlgebraComplex.toComplex_ofComplex** 是 Mathlib 中的一个定理，位于命名空间 `Clifford
AlgebraComplex`。
形式化陈述：toComplex_ofComplex (c : Complex) : toComplex (ofComplex c) = c
参数：c : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `CliffordAlgebraComplex.toComplex_comp_ofComplex`：toComplex_comp_ofComple
x : toComplex.comp ofComplex = AlgHom.id Real Complex
-/
theorem toComplex_ofComplex (c : ℂ) : toComplex (ofComplex c) = c :=
  AlgHom.congr_fun toComplex_comp_ofComplex c

@[simp]
/-
**CliffordAlgebraComplex.ofComplex_comp_toComplex** 是 Mathlib 中的一个定理，位于命名空间 `Cli
ffordAlgebraComplex`。
形式化陈述：ofComplex_comp_toComplex : ofComplex.comp toComplex = AlgHom.id Real (Clif
fordAlgebra Q)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] 
{f g : CliffordAlgebra Q ->ₐ[R] A} : f.toLinearMap.comp (ι Q) = g.toLinearMap.co
mp (ι Q) -> f…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebraComplex.toComplex_ι`：toComplex_ι (r : Real) : toComplex (
ι Q r) = r • Complex.I
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `CliffordAlgebraComplex.ofComplex_I`：ofComplex_I : ofComplex Complex.I = 
ι Q 1
-/
theorem ofComplex_comp_toComplex : ofComplex.comp toComplex = AlgHom.id ℝ (CliffordAlgebra Q) := by
  ext
  dsimp only [LinearMap.comp_apply, Subtype.coe_mk, AlgHom.id_apply, AlgHom.toLinearMap_apply,
    AlgHom.comp_apply]
  rw [toComplex_ι, one_smul, ofComplex_I]

@[simp]
/-
**CliffordAlgebraComplex.ofComplex_toComplex** 是 Mathlib 中的一个定理，位于命名空间 `Clifford
AlgebraComplex`。
形式化陈述：ofComplex_toComplex (c : CliffordAlgebra Q) : ofComplex (toComplex c) = c
参数：c : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `CliffordAlgebraComplex.ofComplex_comp_toComplex`：ofComplex_comp_toComple
x : ofComplex.comp toComplex = AlgHom.id Real (CliffordAlgebra Q)
-/
theorem ofComplex_toComplex (c : CliffordAlgebra Q) : ofComplex (toComplex c) = c :=
  AlgHom.congr_fun ofComplex_comp_toComplex c

/-- The clifford algebras over `CliffordAlgebraComplex.Q` is isomorphic as an `ℝ`-algebra to `ℂ`. -/
@[simps!]
/-
**CliffordAlgebraComplex.equiv** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebraComplex
`。
形式化陈述：CliffordAlgebra CliffordAlgebraComplex.Q ≃ₐ[ℝ] ℂ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebraComplex.toComplex_comp_ofComplex`：toComplex_comp_ofComple
x : toComplex.comp ofComplex = AlgHom.id Real Complex
· 使用定理 `CliffordAlgebraComplex.ofComplex_comp_toComplex`：ofComplex_comp_toComple
x : ofComplex.comp toComplex = AlgHom.id Real (CliffordAlgebra Q)

--- 原说明 ---
The clifford algebras over `CliffordAlgebraComplex.Q` is isomorphic as an `ℝ`-al
gebra to `ℂ`.
-/
protected def equiv : CliffordAlgebra Q ≃ₐ[ℝ] ℂ :=
  AlgEquiv.ofAlgHom toComplex ofComplex toComplex_comp_ofComplex ofComplex_comp_toComplex

/-- The clifford algebra is commutative since it is isomorphic to the complex numbers.

TODO: prove this is true for all `CliffordAlgebra`s over a 1-dimensional vector space. -/
/-
**CliffordAlgebraComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CliffordAlgebraComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The clifford algebra is commutative since it is isomorphic to the complex number
s.

TODO: prove this is true for all `CliffordAlgebra`s over a 1-dimensional vector 
space.
-/
instance : CommRing (CliffordAlgebra Q) where
  mul_comm := fun x y =>
    CliffordAlgebraComplex.equiv.injective <| by
      rw [map_mul, mul_comm, map_mul]

/-- `reverse` is a no-op over `CliffordAlgebraComplex.Q`. -/
/-
**CliffordAlgebraComplex.reverse_apply** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebr
aComplex`。
形式化陈述：reverse_apply (x : CliffordAlgebra Q) : x.reverse = x
参数：x : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.induction`：induction {C : CliffordAlgebra Q -> Prop} (al
gebraMap : forall r, C (algebraMap R (CliffordAlgebra Q) r)) (ι : forall x, C (ι
 Q x)) (mul : f…
· 使用定理 `CliffordAlgebra.reverse.commutes`：∀ {R : Type u_1} [inst : CommRing R] {
M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Quad
raticForm R M} (r : R)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.reverse_ι`：reverse_ι (m : M) : reverse (ι Q m) = ι Q m
· 使用定理 `CliffordAlgebra.reverse.map_mul`：∀ {R : Type u_1} [inst : CommRing R] {M
 : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Quadr
aticForm R M} (a b : …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…

--- 原说明 ---
`reverse` is a no-op over `CliffordAlgebraComplex.Q`.
-/
theorem reverse_apply (x : CliffordAlgebra Q) : x.reverse = x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact reverse.commutes _
  | ι x => rw [reverse_ι]
  | mul x₁ x₂ hx₁ hx₂ => rw [reverse.map_mul, mul_comm, hx₁, hx₂]
  | add x₁ x₂ hx₁ hx₂ => rw [reverse.map_add, hx₁, hx₂]

@[simp]
/-
**CliffordAlgebraComplex.reverse_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebr
aComplex`。
形式化陈述：reverse_eq_id : (reverse : CliffordAlgebra Q ->ₗ[Real] _) = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `CliffordAlgebraComplex.reverse_apply`：reverse_apply (x : CliffordAlgebra
 Q) : x.reverse = x
-/
theorem reverse_eq_id : (reverse : CliffordAlgebra Q →ₗ[ℝ] _) = LinearMap.id :=
  LinearMap.ext reverse_apply

/-- `Complex.conj` is analogous to `CliffordAlgebra.involute`. -/
@[simp]
/-
**CliffordAlgebraComplex.ofComplex_conj** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgeb
raComplex`。
形式化陈述：ofComplex_conj (c : Complex) : ofComplex (conj c) = involute (ofComplex c)
参数：c : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebraComplex.equiv_apply`：∀ (a : CliffordAlgebra CliffordAlgeb
raComplex.Q), CliffordAlgebraComplex.equiv a = CliffordAlgebraComplex.toComplex 
a
· 使用定理 `CliffordAlgebraComplex.toComplex_involute`：toComplex_involute (c : Cliff
ordAlgebra Q) : toComplex (involute c) = conj (toComplex c)
· 使用定理 `CliffordAlgebraComplex.toComplex_ofComplex`：toComplex_ofComplex (c : Com
plex) : toComplex (ofComplex c) = c

--- 原说明 ---
`Complex.conj` is analogous to `CliffordAlgebra.involute`.
-/
theorem ofComplex_conj (c : ℂ) : ofComplex (conj c) = involute (ofComplex c) :=
  CliffordAlgebraComplex.equiv.injective <| by
    rw [equiv_apply, equiv_apply, toComplex_involute, toComplex_ofComplex, toComplex_ofComplex]

end CliffordAlgebraComplex

/-! ### The clifford algebra isomorphic to the quaternions -/


namespace CliffordAlgebraQuaternion

open scoped Quaternion

open QuaternionAlgebra

variable {R : Type*} [CommRing R] (c₁ c₂ : R)

/-- `Q c₁ c₂` is a quadratic form over `R × R` such that `CliffordAlgebra (Q c₁ c₂)` is isomorphic
as an `R`-algebra to `ℍ[R,c₁,c₂]`. -/
/-
**CliffordAlgebraQuaternion.Q** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebraQuaterni
on`。
形式化陈述：Q : QuadraticForm R (R × R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Q c₁ c₂` is a quadratic form over `R × R` such that `CliffordAlgebra (Q c₁ c₂)`
 is isomorphic
as an `R`-algebra to `ℍ[R,c₁,c₂]`.
-/
def Q : QuadraticForm R (R × R) :=
  (c₁ • QuadraticMap.sq).prod (c₂ • QuadraticMap.sq)

@[simp]
/-
**CliffordAlgebraQuaternion.Q_apply** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebraQu
aternion`。
形式化陈述：Q_apply (v : R × R) : Q c₁ c₂ v = c₁ * (v.1 * v.1) + c₂ * (v.2 * v.2)
参数：v : R × R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Q_apply (v : R × R) : Q c₁ c₂ v = c₁ * (v.1 * v.1) + c₂ * (v.2 * v.2) :=
  rfl

/-- The quaternion basis vectors within the algebra. -/
@[simps i j k]
/-
**CliffordAlgebraQuaternion.quaternionBasis** 是 Mathlib 中的一个定义，位于命名空间 `CliffordA
lgebraQuaternion`。
形式化陈述：quaternionBasis : QuaternionAlgebra.Basis (CliffordAlgebra (Q c₁ c₂)) c₁ 0
 c₂ where i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quaternion basis vectors within the algebra.
-/
def quaternionBasis : QuaternionAlgebra.Basis (CliffordAlgebra (Q c₁ c₂)) c₁ 0 c₂ where
  i := ι (Q c₁ c₂) (1, 0)
  j := ι (Q c₁ c₂) (0, 1)
  k := ι (Q c₁ c₂) (1, 0) * ι (Q c₁ c₂) (0, 1)
  i_mul_i := by
    rw [ι_sq_scalar, Q_apply, ← Algebra.algebraMap_eq_smul_one]
    simp
  j_mul_j := by
    rw [ι_sq_scalar, Q_apply, ← Algebra.algebraMap_eq_smul_one]
    simp
  i_mul_j := rfl
  j_mul_i := by
    rw [zero_smul, zero_sub, eq_neg_iff_add_eq_zero, ι_mul_ι_add_swap, QuadraticMap.polar]
    simp

variable {c₁ c₂}

/-- Intermediate result of `CliffordAlgebraQuaternion.equiv`: clifford algebras over
`CliffordAlgebraQuaternion.Q` can be converted to `ℍ[R,c₁,c₂]`. -/
/-
**CliffordAlgebraQuaternion.toQuaternion** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlge
braQuaternion`。
形式化陈述：toQuaternion : CliffordAlgebra (Q c₁ c₂) ->ₐ[R] ℍ[R,c₁,0,c₂]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Intermediate result of `CliffordAlgebraQuaternion.equiv`: clifford algebras over
`CliffordAlgebraQuaternion.Q` can be converted to `ℍ[R,c₁,c₂]`.
-/
def toQuaternion : CliffordAlgebra (Q c₁ c₂) →ₐ[R] ℍ[R,c₁,0,c₂] :=
  CliffordAlgebra.lift (Q c₁ c₂)
    ⟨{  toFun := fun v => (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,0,c₂])
        map_add' := fun v₁ v₂ => by simp
        map_smul' := fun r v => by dsimp; rw [mul_zero] }, fun v => by
      dsimp
      ext
      all_goals dsimp; ring⟩

@[simp]
/-
**CliffordAlgebraQuaternion.toQuaternion_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlg
ebraQuaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toQuaternion_ι (v : R × R) :
    toQuaternion (ι (Q c₁ c₂) v) = (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,0,c₂]) :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-- The "clifford conjugate" maps to the quaternion conjugate. -/
/-
**CliffordAlgebraQuaternion.toQuaternion_star** 是 Mathlib 中的一个定理，位于命名空间 `Cliffor
dAlgebraQuaternion`。
形式化陈述：toQuaternion_star (c : CliffordAlgebra (Q c₁ c₂)) : toQuaternion (star c) 
= star (toQuaternion c)
参数：c : CliffordAlgebra (Q c₁ c₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.star_def'`：star_def' (x : CliffordAlgebra Q) : star x = 
involute (reverse x)
· 使用定理 `CliffordAlgebra.induction`：induction {C : CliffordAlgebra Q -> Prop} (al
gebraMap : forall r, C (algebraMap R (CliffordAlgebra Q) r)) (ι : forall x, C (ι
 Q x)) (mul : f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CliffordAlgebra.reverse.commutes`：∀ {R : Type u_1} [inst : CommRing R] {
M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Quad
raticForm R M} (r : R)…
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `QuaternionAlgebra.star_coe`：star_coe : star (x : ℍ[R,c₁,c₂,c₃]) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CliffordAlgebra.reverse_ι`：reverse_ι (m : M) : reverse (ι Q m) = ι Q m
· 使用定理 `CliffordAlgebra.involute_ι`：involute_ι (m : M) : involute (ι Q m) = -ι Q
 m
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `CliffordAlgebraQuaternion.toQuaternion_ι`：toQuaternion_ι (v : R × R) : t
oQuaternion (ι (Q c₁ c₂) v) = (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,0,c₂])
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CliffordAlgebra.reverse.map_mul`：∀ {R : Type u_1} [inst : CommRing R] {M
 : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Quadr
aticForm R M} (a b : …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s

--- 原说明 ---
The "clifford conjugate" maps to the quaternion conjugate.
-/
theorem toQuaternion_star (c : CliffordAlgebra (Q c₁ c₂)) :
    toQuaternion (star c) = star (toQuaternion c) := by
  simp only [CliffordAlgebra.star_def']
  induction c using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι x => simp
  | mul x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂]
  | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂]

/-- Map a quaternion into the clifford algebra. -/
/-
**CliffordAlgebraQuaternion.ofQuaternion** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlge
braQuaternion`。
形式化陈述：ofQuaternion : ℍ[R,c₁,0,c₂] ->ₐ[R] CliffordAlgebra (Q c₁ c₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a quaternion into the clifford algebra.
-/
def ofQuaternion : ℍ[R,c₁,0,c₂] →ₐ[R] CliffordAlgebra (Q c₁ c₂) :=
  (quaternionBasis c₁ c₂).liftHom

@[simp]
/-
**CliffordAlgebraQuaternion.ofQuaternion_mk** 是 Mathlib 中的一个定理，位于命名空间 `CliffordA
lgebraQuaternion`。
形式化陈述：ofQuaternion_mk (a₁ a₂ a₃ a₄ : R) : ofQuaternion (⟨a₁, a₂, a₃, a₄⟩ : ℍ[R,c
₁,0,c₂]) = algebraMap R _ a₁ + a₂ • ι (Q c₁ c₂) (1, 0) + a₃ • ι (Q c₁ c₂) (0, 1)
 + a₄ • (ι (Q c₁ c₂) (1, 0) * ι (Q c₁ c₂) (0, 1))
参数：a₁ a₂ a₃ a₄ : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofQuaternion_mk (a₁ a₂ a₃ a₄ : R) :
    ofQuaternion (⟨a₁, a₂, a₃, a₄⟩ : ℍ[R,c₁,0,c₂]) =
      algebraMap R _ a₁ + a₂ • ι (Q c₁ c₂) (1, 0) + a₃ • ι (Q c₁ c₂) (0, 1) +
        a₄ • (ι (Q c₁ c₂) (1, 0) * ι (Q c₁ c₂) (0, 1)) :=
  rfl

@[simp]
/-
**CliffordAlgebraQuaternion.ofQuaternion_comp_toQuaternion** 是 Mathlib 中的一个定理，位于
命名空间 `CliffordAlgebraQuaternion`。
形式化陈述：ofQuaternion_comp_toQuaternion : ofQuaternion.comp toQuaternion = AlgHom.i
d R (CliffordAlgebra (Q c₁ c₂))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] 
{f g : CliffordAlgebra Q ->ₐ[R] A} : f.toLinearMap.comp (ι Q) = g.toLinearMap.co
mp (ι Q) -> f…
· 使用定理 `LinearMap.prod_ext`：prod_ext {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl 
_ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f 
= g
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebraQuaternion.toQuaternion_ι`：toQuaternion_ι (v : R × R) : t
oQuaternion (ι (Q c₁ c₂) v) = (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,0,c₂])
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofQuaternion_comp_toQuaternion :
    ofQuaternion.comp toQuaternion = AlgHom.id R (CliffordAlgebra (Q c₁ c₂)) := by
  ext : 2 <;> (ext; simp)

@[simp]
/-
**CliffordAlgebraQuaternion.ofQuaternion_toQuaternion** 是 Mathlib 中的一个定理，位于命名空间 
`CliffordAlgebraQuaternion`。
形式化陈述：ofQuaternion_toQuaternion (c : CliffordAlgebra (Q c₁ c₂)) : ofQuaternion (
toQuaternion c) = c
参数：c : CliffordAlgebra (Q c₁ c₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `CliffordAlgebraQuaternion.ofQuaternion_comp_toQuaternion`：ofQuaternion_c
omp_toQuaternion : ofQuaternion.comp toQuaternion = AlgHom.id R (CliffordAlgebra
 (Q c₁ c₂))
-/
theorem ofQuaternion_toQuaternion (c : CliffordAlgebra (Q c₁ c₂)) :
    ofQuaternion (toQuaternion c) = c :=
  AlgHom.congr_fun ofQuaternion_comp_toQuaternion c

@[simp]
/-
**CliffordAlgebraQuaternion.toQuaternion_comp_ofQuaternion** 是 Mathlib 中的一个定理，位于
命名空间 `CliffordAlgebraQuaternion`。
形式化陈述：toQuaternion_comp_ofQuaternion : toQuaternion.comp ofQuaternion = AlgHom.i
d R ℍ[R,c₁,0,c₂]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuaternionAlgebra.hom_ext`：hom_ext ⦃f g : ℍ[R,c₁,c₂,c₃] ->ₐ[R] A⦄ (hi : 
f (Basis.self R).i = g (Basis.self R).i) (hj : f (Basis.self R).j = g (Basis.sel
f R).j) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuaternionAlgebra.Basis.i_self`：∀ (R : Type u_1) [inst : CommRing R] {c₁
 c₂ c₃ : R},   (QuaternionAlgebra.Basis.self R).i = { re := 0, imI := 1, imJ := 
0, imK := 0 }
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CliffordAlgebraQuaternion.toQuaternion_ι`：toQuaternion_ι (v : R × R) : t
oQuaternion (ι (Q c₁ c₂) v) = (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,0,c₂])
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `QuaternionAlgebra.Basis.j_self`：∀ (R : Type u_1) [inst : CommRing R] {c₁
 c₂ c₃ : R},   (QuaternionAlgebra.Basis.self R).j = { re := 0, imI := 0, imJ := 
1, imK := 0 }
-/
theorem toQuaternion_comp_ofQuaternion :
    toQuaternion.comp ofQuaternion = AlgHom.id R ℍ[R,c₁,0,c₂] := by
  ext : 1 <;> simp

@[simp]
/-
**CliffordAlgebraQuaternion.toQuaternion_ofQuaternion** 是 Mathlib 中的一个定理，位于命名空间 
`CliffordAlgebraQuaternion`。
形式化陈述：toQuaternion_ofQuaternion (q : ℍ[R,c₁,0,c₂]) : toQuaternion (ofQuaternion 
q) = q
参数：q : ℍ[R,c₁,0,c₂]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `CliffordAlgebraQuaternion.toQuaternion_comp_ofQuaternion`：toQuaternion_c
omp_ofQuaternion : toQuaternion.comp ofQuaternion = AlgHom.id R ℍ[R,c₁,0,c₂]
-/
theorem toQuaternion_ofQuaternion (q : ℍ[R,c₁,0,c₂]) : toQuaternion (ofQuaternion q) = q :=
  AlgHom.congr_fun toQuaternion_comp_ofQuaternion q

/-- The clifford algebra over `CliffordAlgebraQuaternion.Q c₁ c₂` is isomorphic as an `R`-algebra
to `ℍ[R,c₁,c₂]`. -/
@[simps!]
/-
**CliffordAlgebraQuaternion.equiv** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebraQuat
ernion`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] →     {c₁ c₂ : R} → CliffordAlgebra
 (CliffordAlgebraQuaternion.Q c₁ c₂) ≃ₐ[R] QuaternionAlgebra R c₁ 0 c₂
参数：CliffordAlgebraQuaternion.Q c₁ c₂。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebraQuaternion.toQuaternion_comp_ofQuaternion`：toQuaternion_c
omp_ofQuaternion : toQuaternion.comp ofQuaternion = AlgHom.id R ℍ[R,c₁,0,c₂]
· 使用定理 `CliffordAlgebraQuaternion.ofQuaternion_comp_toQuaternion`：ofQuaternion_c
omp_toQuaternion : ofQuaternion.comp toQuaternion = AlgHom.id R (CliffordAlgebra
 (Q c₁ c₂))

--- 原说明 ---
The clifford algebra over `CliffordAlgebraQuaternion.Q c₁ c₂` is isomorphic as a
n `R`-algebra
to `ℍ[R,c₁,c₂]`.
-/
protected def equiv : CliffordAlgebra (Q c₁ c₂) ≃ₐ[R] ℍ[R,c₁,0,c₂] :=
  AlgEquiv.ofAlgHom toQuaternion ofQuaternion toQuaternion_comp_ofQuaternion
    ofQuaternion_comp_toQuaternion

/-- The quaternion conjugate maps to the "clifford conjugate" (aka `star`). -/
@[simp]
/-
**CliffordAlgebraQuaternion.ofQuaternion_star** 是 Mathlib 中的一个定理，位于命名空间 `Cliffor
dAlgebraQuaternion`。
形式化陈述：ofQuaternion_star (q : ℍ[R,c₁,0,c₂]) : ofQuaternion (star q) = star (ofQua
ternion q)
参数：q : ℍ[R,c₁,0,c₂]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebraQuaternion.equiv_apply`：∀ {R : Type u_1} [inst : CommRing
 R] {c₁ c₂ : R} (a : CliffordAlgebra (CliffordAlgebraQuaternion.Q c₁ c₂)),   Cli
ffordAlgebraQuaternion.equi…
· 使用定理 `CliffordAlgebraQuaternion.toQuaternion_star`：toQuaternion_star (c : Clif
fordAlgebra (Q c₁ c₂)) : toQuaternion (star c) = star (toQuaternion c)
· 使用定理 `CliffordAlgebraQuaternion.toQuaternion_ofQuaternion`：toQuaternion_ofQuat
ernion (q : ℍ[R,c₁,0,c₂]) : toQuaternion (ofQuaternion q) = q

--- 原说明 ---
The quaternion conjugate maps to the "clifford conjugate" (aka `star`).
-/
theorem ofQuaternion_star (q : ℍ[R,c₁,0,c₂]) : ofQuaternion (star q) = star (ofQuaternion q) :=
  CliffordAlgebraQuaternion.equiv.injective <| by
    rw [equiv_apply, equiv_apply, toQuaternion_star, toQuaternion_ofQuaternion,
      toQuaternion_ofQuaternion]

end CliffordAlgebraQuaternion

/-! ### The clifford algebra isomorphic to the dual numbers -/


namespace CliffordAlgebraDualNumber

open scoped DualNumber

open DualNumber TrivSqZeroExt

variable {R : Type*} [CommRing R]

/-
**CliffordAlgebraDualNumber.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebraDualNumbe
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_mul_ι (r₁ r₂) : ι (0 : QuadraticForm R R) r₁ * ι (0 : QuadraticForm R R) r₂ = 0 := by
  rw [← mul_one r₁, ← mul_one r₂, ← smul_eq_mul r₁, ← smul_eq_mul r₂, map_smul, map_smul,
    smul_mul_smul_comm, ι_sq_scalar, zero_apply, map_zero, smul_zero]

set_option backward.isDefEq.respectTransparency.types false in
/-- The clifford algebra over a 1-dimensional vector space with 0 quadratic form is isomorphic to
the dual numbers. -/
/-
**CliffordAlgebraDualNumber.equiv** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebraDual
Number`。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → CliffordAlgebra 0 ≃ₐ[R] DualNumber 
R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The clifford algebra over a 1-dimensional vector space with 0 quadratic form is 
isomorphic to
the dual numbers.
-/
protected def equiv : CliffordAlgebra (0 : QuadraticForm R R) ≃ₐ[R] R[ε] :=
  AlgEquiv.ofAlgHom
    (CliffordAlgebra.lift (0 : QuadraticForm R R) ⟨inrHom R _, fun m => inr_mul_inr _ m m⟩)
    (DualNumber.lift ⟨
      (Algebra.ofId _ _, ι (R := R) _ 1),
      ι_mul_ι (1 : R) 1,
      fun _ => (Algebra.commutes _ _).symm⟩)
    (by ext : 1; simp) (by ext : 2; simp)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CliffordAlgebraDualNumber.equiv_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebraDua
lNumber`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_ι (r : R) : CliffordAlgebraDualNumber.equiv (ι (R := R) _ r) = r • ε := by
  dsimp [CliffordAlgebraDualNumber.equiv, AlgEquiv.ofAlgHom]
  exact (lift_ι_apply _ _ r).trans (inr_eq_smul_eps _)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CliffordAlgebraDualNumber.equiv_symm_eps** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAl
gebraDualNumber`。
形式化陈述：equiv_symm_eps : CliffordAlgebraDualNumber.equiv.symm (eps : R[ε]) = ι (0 
: QuadraticForm R R) 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `DualNumber.lift_apply_eps`：∀ {R : Type u_1} {B : Type u_3} {A : Type u_4
} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 
: Algebra R A] …
-/
theorem equiv_symm_eps :
    CliffordAlgebraDualNumber.equiv.symm (eps : R[ε]) = ι (0 : QuadraticForm R R) 1 := by
  dsimp [CliffordAlgebraDualNumber.equiv, AlgEquiv.ofAlgHom]
  exact DualNumber.lift_apply_eps _

end CliffordAlgebraDualNumber

