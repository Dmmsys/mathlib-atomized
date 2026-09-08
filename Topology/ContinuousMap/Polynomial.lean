/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.Topology.UnitInterval
public import Mathlib.Algebra.Star.Subalgebra

/-!
# Constructions relating polynomial functions and continuous functions.

## Main definitions

* `Polynomial.toContinuousMapOn p X`: for `X : Set R`, interprets a polynomial `p`
  as a bundled continuous function in `C(X, R)`.
* `Polynomial.toContinuousMapOnAlgHom`: the same, as an `R`-algebra homomorphism.
* `polynomialFunctions (X : Set R) : Subalgebra R C(X, R)`: polynomial functions as a subalgebra.
* `polynomialFunctions_separatesPoints (X : Set R) : (polynomialFunctions X).SeparatesPoints`:
  the polynomial functions separate points.

-/

@[expose] public section


variable {R : Type*}

open Polynomial

namespace Polynomial

section

variable [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R]

/--
Every polynomial with coefficients in a topological semiring gives a (bundled) continuous function.
-/
@[simps]
/-
**Polynomial.toContinuousMap** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：toContinuousMap (p : R[X]) : C(R, R)
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every polynomial with coefficients in a topological semiring gives a (bundled) c
ontinuous function.
-/
def toContinuousMap (p : R[X]) : C(R, R) :=
  ⟨fun x : R => p.eval x, by fun_prop⟩

open ContinuousMap in
/-
**Polynomial.toContinuousMap_X_eq_id** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：toContinuousMap_X_eq_id : X.toContinuousMap = .id R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.toContinuousMap_apply`：∀ {R : Type u_1} [inst : Semiring R] [
inst_1 : TopologicalSpace R] [inst_2 : IsTopologicalSemiring R] (p : Polynomial 
R)   (x : R), p.toCont…
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toContinuousMap_X_eq_id : X.toContinuousMap = .id R := by
  ext; simp

/-- A polynomial as a continuous function,
with domain restricted to some subset of the semiring of coefficients.

(This is particularly useful when restricting to compact sets, e.g. `[0,1]`.)
-/
@[simps]
/-
**Polynomial.toContinuousMapOn** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：toContinuousMapOn (p : R[X]) (X : Set R) : C(X, R)
参数：p : R[X]；X : Set R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A polynomial as a continuous function,
with domain restricted to some subset of the semiring of coefficients.

(This is particularly useful when restricting to compact sets, e.g. `[0,1]`.)
-/
def toContinuousMapOn (p : R[X]) (X : Set R) : C(X, R) :=
  ⟨fun x : X => p.toContinuousMap x, by fun_prop⟩

open ContinuousMap in
/-
**Polynomial.toContinuousMapOn_X_eq_restrict_id** 是 Mathlib 中的一个引理，位于命名空间 `Polyn
omial`。
形式化陈述：toContinuousMapOn_X_eq_restrict_id (s : Set R) : X.toContinuousMapOn s = r
estrict s (.id R)
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.toContinuousMapOn_apply`：∀ {R : Type u_1} [inst : Semiring R]
 [inst_1 : TopologicalSpace R] [inst_2 : IsTopologicalSemiring R] (p : Polynomia
l R)   (X : Set R) (x : …
· 使用定理 `Polynomial.toContinuousMap_apply`：∀ {R : Type u_1} [inst : Semiring R] [
inst_1 : TopologicalSpace R] [inst_2 : IsTopologicalSemiring R] (p : Polynomial 
R)   (x : R), p.toCont…
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toContinuousMapOn_X_eq_restrict_id (s : Set R) :
    X.toContinuousMapOn s = restrict s (.id R) := by
  ext; simp


-- TODO some lemmas about when `toContinuousMapOn` is injective?
end

section

variable {α : Type*} [TopologicalSpace α] [CommSemiring R] [TopologicalSpace R]
  [IsTopologicalSemiring R]

@[simp]
/-
**Polynomial.aeval_continuousMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_continuousMap_apply (g : R[X]) (f : C(α, R)) (x : α) : ((Polynomial.
aeval f) g) x = g.eval (f x)
参数：g : R[X]；f : C(α, R)；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.aeval_monomial`：aeval_monomial {n : Nat} {r : R} : aeval x (m
onomial n r) = algebraMap _ _ r * x ^ n
· 使用定理 `algebraMap_apply`：algebraMap_apply (k : R) (a : α) : algebraMap R C(α, A
) k a = k • (1 : A)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.eval_monomial`：eval_monomial {n a} : (monomial n a).eval x = 
a * x ^ n
-/
theorem aeval_continuousMap_apply (g : R[X]) (f : C(α, R)) (x : α) :
    ((Polynomial.aeval f) g) x = g.eval (f x) := by
  refine Polynomial.induction_on' g ?_ ?_
  · intro p q hp hq
    simp [hp, hq]
  · intro n a
    simp

end

noncomputable section

variable [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]

/-- The algebra map from `R[X]` to continuous functions `C(R, R)`.
-/
@[simps]
/-
**Polynomial.toContinuousMapAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：toContinuousMapAlgHom : R[X] ->ₐ[R] C(R, R) where toFun p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra map from `R[X]` to continuous functions `C(R, R)`.
-/
def toContinuousMapAlgHom : R[X] →ₐ[R] C(R, R) where
  toFun p := p.toContinuousMap
  map_zero' := by
    ext
    simp
  map_add' _ _ := by
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp
  commutes' _ := by
    ext
    simp [Algebra.algebraMap_eq_smul_one]

/-- The algebra map from `R[X]` to continuous functions `C(X, R)`, for any subset `X` of `R`.
-/
@[simps]
/-
**Polynomial.toContinuousMapOnAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：toContinuousMapOnAlgHom (X : Set R) : R[X] ->ₐ[R] C(X, R) where toFun p
参数：X : Set R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra map from `R[X]` to continuous functions `C(X, R)`, for any subset `X
` of `R`.
-/
def toContinuousMapOnAlgHom (X : Set R) : R[X] →ₐ[R] C(X, R) where
  toFun p := p.toContinuousMapOn X
  map_zero' := by
    ext
    simp
  map_add' _ _ := by
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp
  commutes' _ := by
    ext
    simp [Algebra.algebraMap_eq_smul_one]

end

end Polynomial

section

variable [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]

/--
The subalgebra of polynomial functions in `C(X, R)`, for `X` a subset of some topological semiring
`R`.
-/
noncomputable
/-
**polynomialFunctions** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：polynomialFunctions (X : Set R) : Subalgebra R C(X, R)
参数：X : Set R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def polynomialFunctions (X : Set R) : Subalgebra R C(X, R) :=
  (⊤ : Subalgebra R R[X]).map (Polynomial.toContinuousMapOnAlgHom X)

@[simp]
/-
**polynomialFunctions_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：polynomialFunctions_coe (X : Set R) : (polynomialFunctions X : Set C(X, R)
) = Set.range (Polynomial.toContinuousMapOnAlgHom X)
参数：X : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `AlgHom.coe_range`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] 
[inst_…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.toContinuousMapOnAlgHom_apply`：∀ {R : Type u_1} [inst : CommS
emiring R] [inst_1 : TopologicalSpace R] [inst_2 : IsTopologicalSemiring R] (X :
 Set R)   (p : Polynomial R), …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem polynomialFunctions_coe (X : Set R) :
    (polynomialFunctions X : Set C(X, R)) = Set.range (Polynomial.toContinuousMapOnAlgHom X) := by
  ext
  simp [polynomialFunctions]

set_option backward.defeqAttrib.useBackward true in
-- TODO:
-- if `f : R → R` is an affine equivalence, then pulling back along `f`
-- induces a normed algebra isomorphism between `polynomialFunctions X` and
-- `polynomialFunctions (f ⁻¹' X)`, intertwining the pullback along `f` of `C(R, R)` to itself.
/-
**polynomialFunctions_separatesPoints** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：polynomialFunctions_separatesPoints (X : Set R) : (polynomialFunctions X).
SeparatesPoints
参数：X : Set R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.mem_top`：mem_top {x : A} : x in (⊤ : Subalgebra R A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem polynomialFunctions_separatesPoints (X : Set R) : (polynomialFunctions X).SeparatesPoints :=
  fun x y h => by
  -- We use `Polynomial.X`, then clean up.
  refine ⟨_, ⟨⟨_, ⟨⟨Polynomial.X, ⟨Algebra.mem_top, rfl⟩⟩, rfl⟩⟩, ?_⟩⟩
  dsimp; simp only [Polynomial.eval_X]
  exact fun h' => h (Subtype.ext h')

open unitInterval

open ContinuousMap

set_option backward.defeqAttrib.useBackward true in
/-- The preimage of polynomials on `[0,1]` under the pullback map by `x ↦ (b-a) * x + a`
is the polynomials on `[a,b]`. -/
/-
**polynomialFunctions.comap_compRightAlgHom_iccHomeoI** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：polynomialFunctions.comap_compRightAlgHom_iccHomeoI (a b : Real) (h : a < 
b) : (polynomialFunctions I).comap (compRightAlgHom Real Real (iccHomeoI a b h).
symm) = polynomialFunctions (Set.Icc a b)
参数：a b : Real；h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_smul`：eval_smul [SMulZeroClass S R] [IsScalarTower S R R
] (s : S) (p : R[X]) (x : R) : (s • p).eval x = s • p.eval x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
（共 105 条，此处仅展示前 30 条）

--- 原说明 ---
The preimage of polynomials on `[0,1]` under the pullback map by `x ↦ (b-a) * x 
+ a`
is the polynomials on `[a,b]`.
-/
theorem polynomialFunctions.comap_compRightAlgHom_iccHomeoI (a b : ℝ) (h : a < b) :
    (polynomialFunctions I).comap (compRightAlgHom ℝ ℝ (iccHomeoI a b h).symm) =
      polynomialFunctions (Set.Icc a b) := by
  ext f
  fconstructor
  · rintro ⟨p, ⟨-, w⟩⟩
    rw [DFunLike.ext_iff] at w
    dsimp at w
    let q := p.comp ((b - a)⁻¹ • Polynomial.X + Polynomial.C (-a * (b - a)⁻¹))
    refine ⟨q, ⟨?_, ?_⟩⟩
    · simp
    · ext x
      simp only [q, neg_mul, map_neg, map_mul, AlgHom.coe_toRingHom,
        Polynomial.eval_X, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_smul,
        smul_eq_mul, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_comp, Polynomial.toContinuousMapOnAlgHom_apply,
        Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply]
      convert! w ⟨_, _⟩
      · ext
        simp only [iccHomeoI_symm_apply_coe]
        replace h : b - a ≠ 0 := sub_ne_zero_of_ne h.ne.symm
        field
      · rw [mul_comm (b - a)⁻¹, ← neg_mul, ← add_mul, ← sub_eq_add_neg]
        have w₁ : 0 < (b - a)⁻¹ := inv_pos.mpr (sub_pos.mpr h)
        have w₂ : 0 ≤ (x : ℝ) - a := sub_nonneg.mpr x.2.1
        have w₃ : (x : ℝ) - a ≤ b - a := sub_le_sub_right x.2.2 a
        fconstructor
        · exact mul_nonneg w₂ (le_of_lt w₁)
        · rw [← div_eq_mul_inv, div_le_one (sub_pos.mpr h)]
          exact w₃
  · rintro ⟨p, ⟨-, rfl⟩⟩
    let q := p.comp ((b - a) • Polynomial.X + Polynomial.C a)
    refine ⟨q, ⟨?_, ?_⟩⟩
    · simp
    · ext x
      simp [q, mul_comm]
/-
**polynomialFunctions.eq_adjoin_X** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：polynomialFunctions.eq_adjoin_X (s : Set R) : polynomialFunctions s = Alge
bra.adjoin R {toContinuousMapOnAlgHom s X}
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.coe_toRingHom`：coe_toRingHom (f : A ->ₐ[R] B) : ⇑(f : A ->+* B) =
 f
· 使用定理 `Polynomial.induction_on`：∀ {R : Type u} [inst : Semiring R] {motive : Po
lynomial R → Prop} (p : Polynomial R),   (∀ (a : R), motive (Polynomial.C a)) → 
    (∀ (p q :…
· 使用定理 `Polynomial.C_eq_algebraMap`：C_eq_algebraMap (r : R) : C r = algebraMap R
 R[X] r
· 使用定理 `AlgHomClass.commutes`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A : ou
tParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {inst_1 :
 Semiring …
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
（共 34 条，此处仅展示前 30 条）
-/
theorem polynomialFunctions.eq_adjoin_X (s : Set R) :
    polynomialFunctions s = Algebra.adjoin R {toContinuousMapOnAlgHom s X} := by
  refine le_antisymm ?_
    (Algebra.adjoin_le fun _ h => ⟨X, trivial, (Set.mem_singleton_iff.1 h).symm⟩)
  rintro - ⟨p, -, rfl⟩
  rw [AlgHom.coe_toRingHom]
  refine p.induction_on (fun r => ?_) (fun f g hf hg => ?_) fun n r hn => ?_
  · rw [Polynomial.C_eq_algebraMap, AlgHomClass.commutes]
    exact Subalgebra.algebraMap_mem _ r
  · rw [map_add]
    exact add_mem hf hg
  · rw [pow_succ, ← mul_assoc, map_mul]
    exact mul_mem hn (Algebra.subset_adjoin <| Set.mem_singleton _)
/-
**polynomialFunctions.le_equalizer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：polynomialFunctions.le_equalizer {A : Type*} [Semiring A] [Algebra R A] (s
 : Set R) (φ ψ : C(s, R) ->ₐ[R] A) (h : φ (toContinuousMapOnAlgHom s X) = ψ (toC
ontinuousMapOnAlgHom s X)) : polynomialFunctions s <= AlgHom.equalizer φ ψ
参数：s : Set R；φ ψ : C(s, R) ->ₐ[R] A；h : φ (toContinuousMapOnAlgHom s X) = ψ (toC
ontinuousMapOnAlgHom s X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `polynomialFunctions.eq_adjoin_X`：polynomialFunctions.eq_adjoin_X (s : Se
t R) : polynomialFunctions s = Algebra.adjoin R {toContinuousMapOnAlgHom s X}
· 使用定理 `AlgHom.adjoin_le_equalizer`：adjoin_le_equalizer (φ₁ φ₂ : A ->ₐ[R] B) {s 
: Set A} (h : s.EqOn φ₁ φ₂) : adjoin R s <= equalizer φ₁ φ₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem polynomialFunctions.le_equalizer {A : Type*} [Semiring A] [Algebra R A] (s : Set R)
    (φ ψ : C(s, R) →ₐ[R] A)
    (h : φ (toContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) :
    polynomialFunctions s ≤ AlgHom.equalizer φ ψ := by
  rw [polynomialFunctions.eq_adjoin_X s]
  exact φ.adjoin_le_equalizer ψ fun x hx => (Set.mem_singleton_iff.1 hx).symm ▸ h

open StarAlgebra
/-
**polynomialFunctions.starClosure_eq_adjoin_X** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：polynomialFunctions.starClosure_eq_adjoin_X [StarRing R] [ContinuousStar R
] (s : Set R) : (polynomialFunctions s).starClosure = adjoin R {toContinuousMapO
nAlgHom s X}
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `polynomialFunctions.eq_adjoin_X`：polynomialFunctions.eq_adjoin_X (s : Se
t R) : polynomialFunctions s = Algebra.adjoin R {toContinuousMapOnAlgHom s X}
· 使用定理 `StarAlgebra.adjoin_eq_starClosure_adjoin`：adjoin_eq_starClosure_adjoin (
s : Set A) : adjoin R s = (Algebra.adjoin R s).starClosure
-/
theorem polynomialFunctions.starClosure_eq_adjoin_X [StarRing R] [ContinuousStar R] (s : Set R) :
    (polynomialFunctions s).starClosure = adjoin R {toContinuousMapOnAlgHom s X} := by
  rw [polynomialFunctions.eq_adjoin_X s, adjoin_eq_starClosure_adjoin]
/-
**polynomialFunctions.starClosure_le_equalizer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：polynomialFunctions.starClosure_le_equalizer {A : Type*} [StarRing R] [Con
tinuousStar R] [Semiring A] [StarRing A] [Algebra R A] (s : Set R) (φ ψ : C(s, R
) ->⋆ₐ[R] A) (h : φ (toContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s
 X)) : (polynomialFunctions s).starClosure <= StarAlgHom.equalizer φ ψ
参数：s : Set R；φ ψ : C(s, R) ->⋆ₐ[R] A；h : φ (toContinuousMapOnAlgHom s X) = ψ (to
ContinuousMapOnAlgHom s X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `StarAlgHom.instStarHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u
_4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst
_3 : Star A] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `polynomialFunctions.starClosure_eq_adjoin_X`：polynomialFunctions.starClo
sure_eq_adjoin_X [StarRing R] [ContinuousStar R] (s : Set R) : (polynomialFuncti
ons s).starClosure = adjoin R {to…
· 使用定理 `StarAlgHom.adjoin_le_equalizer`：adjoin_le_equalizer {s : Set A} (h : s.E
qOn f g) : adjoin R s <= StarAlgHom.equalizer f g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem polynomialFunctions.starClosure_le_equalizer {A : Type*} [StarRing R] [ContinuousStar R]
    [Semiring A] [StarRing A] [Algebra R A] (s : Set R) (φ ψ : C(s, R) →⋆ₐ[R] A)
    (h : φ (toContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) :
    (polynomialFunctions s).starClosure ≤ StarAlgHom.equalizer φ ψ := by
  rw [polynomialFunctions.starClosure_eq_adjoin_X s]
  exact StarAlgHom.adjoin_le_equalizer φ ψ fun x hx => (Set.mem_singleton_iff.1 hx).symm ▸ h

end

