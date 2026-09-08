/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Trace

/-!
# Trace for (finite) ring extensions.

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Main definitions

* `Algebra.trace R S x`: the trace of an element `s` of an `R`-algebra `S`
* `Algebra.traceForm R S`: bilinear form sending `x`, `y` to the trace of `x * y`
* `Algebra.traceMatrix R b`: the matrix whose `(i j)`-th element is the trace of `b i * b j`.

## Main results

* `trace_algebraMap_of_basis`, `trace_algebraMap`: if `x : K`, then `Tr_{L/K} x = [L : K] x`
* `trace_trace_of_basis`, `trace_trace`: `Tr_{L/K} (Tr_{F/L} x) = Tr_{F/K} x`

## Implementation notes

Typically, the trace is defined specifically for finite field extensions.
The definition is as general as possible and the assumption that the extension is finite
is added to the lemmas as needed.

We only define the trace for left multiplication (`Algebra.leftMulMatrix`,
i.e. `LinearMap.mulLeft`).
For now, the definitions assume `S` is commutative, so the choice doesn't matter anyway.

## References

* https://en.wikipedia.org/wiki/Field_trace

-/

@[expose] public section


universe w

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
variable {ι : Type w} [Fintype ι]

open Module

open LinearMap (BilinForm)
open LinearMap

open Matrix

open scoped Matrix

namespace Algebra

variable (R S)

/-- The trace of an element `s` of an `R`-algebra is the trace of `(s * ·)`,
as an `R`-linear map. -/
@[stacks 0BIF "Trace"]
/-
**Algebra.trace** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：trace : S ->ₗ[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trace of an element `s` of an `R`-algebra is the trace of `(s * ·)`,
as an `R`-linear map.
-/
noncomputable def trace : S →ₗ[R] R :=
  (LinearMap.trace R S).comp (lmul R S).toLinearMap

variable {S}

-- Not a `simp` lemma since there are more interesting ways to rewrite `trace R S x`,
-- for example `trace_trace`
/-
**Algebra.trace_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：trace_apply (x) : trace R S x = LinearMap.trace R S (lmul R S x)
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trace_apply (x) : trace R S x = LinearMap.trace R S (lmul R S x) :=
  rfl
/-
**Algebra.trace_eq_zero_of_not_exists_basis** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：trace_eq_zero_of_not_exists_basis (h : ¬exists s : Finset S, Nonempty (Bas
is s R S)) : trace R S = 0
参数：h : ¬exists s : Finset S, Nonempty (Basis s R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trace_eq_zero_of_not_exists_basis (h : ¬∃ s : Finset S, Nonempty (Basis s R S)) :
    trace R S = 0 := by ext s; simp [trace_apply, LinearMap.trace, h]

variable {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
/-
**Algebra.trace_eq_matrix_trace** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：trace_eq_matrix_trace [DecidableEq ι] (b : Basis ι R S) (s : S) : trace R 
S s = Matrix.trace (Algebra.leftMulMatrix b s)
参数：b : Basis ι R S；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.trace_apply`：trace_apply (x) : trace R S x = LinearMap.trace R S
 (lmul R S x)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.trace_eq_matrix_trace`：trace_eq_matrix_trace (f : M ->ₗ[R] M) 
: trace R M f = Matrix.trace (LinearMap.toMatrix b b f)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.toMatrix_lmul_eq`：toMatrix_lmul_eq (x : S) : LinearMap.toMatrix 
b b (LinearMap.mulLeft R x) = leftMulMatrix b x
-/
theorem trace_eq_matrix_trace [DecidableEq ι] (b : Basis ι R S) (s : S) :
    trace R S s = Matrix.trace (Algebra.leftMulMatrix b s) := by
  rw [trace_apply, LinearMap.trace_eq_matrix_trace _ b, ← toMatrix_lmul_eq]; rfl

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
/-
**Algebra.trace_algebraMap_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：trace_algebraMap_of_basis (b : Basis ι R S) (x : R) : trace R S (algebraMa
p R S x) = Fintype.card ι • x
参数：b : Basis ι R S；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.trace_apply`：trace_apply (x) : trace R S x = LinearMap.trace R S
 (lmul R S x)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.trace_eq_matrix_trace`：trace_eq_matrix_trace (f : M ->ₗ[R] M) 
: trace R M f = Matrix.trace (LinearMap.toMatrix b b f)
· 使用定理 `Matrix.trace.eq_1`：∀ {n : Type u_3} {R : Type u_6} [inst : Fintype n] [i
nst_1 : AddCommMonoid R] (A : Matrix n n R),   A.trace = ∑ i, A.diag i
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `LinearMap.toMatrix_algebraMap`：LinearMap.toMatrix_algebraMap (x : R) : L
inearMap.toMatrix v₁ v₁ (algebraMap R (Module.End R M₁) x) = scalar n x
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b

--- 原说明 ---
If `x` is in the base field `K`, then the trace is `[L : K] * x`.
-/
theorem trace_algebraMap_of_basis (b : Basis ι R S) (x : R) :
    trace R S (algebraMap R S x) = Fintype.card ι • x := by
  have := Classical.decEq ι
  rw [trace_apply, LinearMap.trace_eq_matrix_trace R b, Matrix.trace]
  convert! Finset.sum_const x
  simp [-coe_lmul_eq_mul]


/-- The trace map from `R` to itself is the identity map. -/
/-
**Algebra.trace_self** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R], Algebra.trace R R = LinearMap.id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Algebra.trace_algebraMap_of_basis`：trace_algebraMap_of_basis (b : Basis 
ι R S) (x : R) : trace R S (algebraMap R S x) = Fintype.card ι • x

--- 原说明 ---
The trace map from `R` to itself is the identity map.
-/
@[simp] theorem trace_self : trace R R = LinearMap.id := by
  ext; simpa using trace_algebraMap_of_basis (.singleton (Fin 1) R) 1
/-
**Algebra.trace_self_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：trace_self_apply (a) : trace R R a = a
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.trace_self`：∀ {R : Type u_1} [inst : CommRing R], Algebra.trace 
R R = LinearMap.id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trace_self_apply (a) : trace R R a = a := by simp

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`.

(If `L` is not finite-dimensional over `K`, then `trace` and `finrank` return `0`.)
-/
@[simp]
/-
**Algebra.trace_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：trace_algebraMap [StrongRankCondition R] [Module.Free R S] (x : R) : trace
 R S (algebraMap R S x) = finrank R S • x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.trace_algebraMap_of_basis`：trace_algebraMap_of_basis (b : Basis 
ι R S) (x : R) : trace R S (algebraMap R S x) = Fintype.card ι • x
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.trace_eq_zero_of_not_exists_basis`：trace_eq_zero_of_not_exists_b
asis (h : ¬exists s : Finset S, Nonempty (Basis s R S)) : trace R S = 0
· 使用定理 `finrank_eq_zero_of_not_exists_basis_finset`：finrank_eq_zero_of_not_exist
s_basis_finset (h : ¬exists s : Finset M, Nonempty (Basis s R M)) : finrank R M 
= 0
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `x` is in the base field `K`, then the trace is `[L : K] * x`.

(If `L` is not finite-dimensional over `K`, then `trace` and `finrank` return `0
`.)
-/
theorem trace_algebraMap [StrongRankCondition R] [Module.Free R S] (x : R) :
    trace R S (algebraMap R S x) = finrank R S • x := by
  by_cases H : ∃ s : Finset S, Nonempty (Basis s R S)
  · rw [trace_algebraMap_of_basis H.choose_spec.some, finrank_eq_card_basis H.choose_spec.some]
  · simp [trace_eq_zero_of_not_exists_basis R H, finrank_eq_zero_of_not_exists_basis_finset H]

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.trace_trace_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：trace_trace_of_basis [Algebra S T] [IsScalarTower R S T] {ι κ : Type*} [Fi
nite ι] [Finite κ] (b : Basis ι R S) (c : Basis κ S T) (x : T) : trace R S (trac
e S T x) = trace R T x
参数：b : Basis ι R S；c : Basis κ S T；x : T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.trace_eq_matrix_trace`：trace_eq_matrix_trace [DecidableEq ι] (b 
: Basis ι R S) (s : S) : trace R S s = Matrix.trace (Algebra.leftMulMatrix b s)
· 使用定理 `Matrix.trace.eq_1`：∀ {n : Type u_3} {R : Type u_6} [inst : Fintype n] [i
nst_1 : AddCommMonoid R] (A : Matrix n n R),   A.trace = ∑ i, A.diag i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.univ_product_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : Fintyp
e α] [inst_1 : Fintype β], Finset.univ ×ˢ Finset.univ = Finset.univ
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Algebra.smulTower_leftMulMatrix`：smulTower_leftMulMatrix (x) (ik jk) : l
eftMulMatrix (b.smulTower c) x ik jk = leftMulMatrix b (leftMulMatrix c x ik.2 j
k.2) ik.1 jk.1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trace_trace_of_basis [Algebra S T] [IsScalarTower R S T] {ι κ : Type*} [Finite ι]
    [Finite κ] (b : Basis ι R S) (c : Basis κ S T) (x : T) :
    trace R S (trace S T x) = trace R T x := by
  have := Classical.decEq ι
  have := Classical.decEq κ
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  rw [trace_eq_matrix_trace (b.smulTower c), trace_eq_matrix_trace b, trace_eq_matrix_trace c,
    Matrix.trace, Matrix.trace, Matrix.trace, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [map_sum, smulTower_leftMulMatrix, Finset.sum_apply, Matrix.diag,
    Finset.sum_apply i (Finset.univ : Finset κ) fun y => leftMulMatrix b (leftMulMatrix c x y y)]
/-
**Algebra.trace_comp_trace_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：trace_comp_trace_of_basis [Algebra S T] [IsScalarTower R S T] {ι κ : Type*
} [Finite ι] [Finite κ] (b : Basis ι R S) (c : Basis κ S T) : (trace R S).comp (
(trace S T).restrictScalars R) = trace R T
参数：b : Basis ι R S；c : Basis κ S T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.restrictScalars_apply`：restrictScalars_apply (fₗ : M ->ₗ[S] M₂
) (x) : restrictScalars R fₗ x = fₗ x
· 使用定理 `Algebra.trace_trace_of_basis`：trace_trace_of_basis [Algebra S T] [IsScal
arTower R S T] {ι κ : Type*} [Finite ι] [Finite κ] (b : Basis ι R S) (c : Basis 
κ S T) (x : T) : t…
-/
theorem trace_comp_trace_of_basis [Algebra S T] [IsScalarTower R S T] {ι κ : Type*} [Finite ι]
    [Finite κ] (b : Basis ι R S) (c : Basis κ S T) :
    (trace R S).comp ((trace S T).restrictScalars R) = trace R T := by
  ext
  rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, trace_trace_of_basis b c]

@[simp]
/-
**Algebra.trace_trace** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：trace_trace [Algebra S T] [IsScalarTower R S T] [Module.Free R S] [Module.
Finite R S] [Module.Free S T] [Module.Finite S T] (x : T) : trace R S (trace S T
 x) = trace R T x
参数：x : T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.trace_trace_of_basis`：trace_trace_of_basis [Algebra S T] [IsScal
arTower R S T] {ι κ : Type*} [Finite ι] [Finite κ] (b : Basis ι R S) (c : Basis 
κ S T) (x : T) : t…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem trace_trace [Algebra S T] [IsScalarTower R S T]
    [Module.Free R S] [Module.Finite R S] [Module.Free S T] [Module.Finite S T] (x : T) :
    trace R S (trace S T x) = trace R T x :=
  trace_trace_of_basis (Module.Free.chooseBasis R S) (Module.Free.chooseBasis S T) x

/-- Let `T / S / R` be a tower of finite extensions of fields. Then
$\text{Trace}_{T/R} = \text{Trace}_{S/R} \circ \text{Trace}_{T/S}$. -/
@[simp, stacks 0BIJ "Trace"]
/-
**Algebra.trace_comp_trace** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：trace_comp_trace [Algebra S T] [IsScalarTower R S T] [Module.Free R S] [Mo
dule.Finite R S] [Module.Free S T] [Module.Finite S T] : (trace R S).comp ((trac
e S T).restrictScalars R) = trace R T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.trace_trace`：trace_trace [Algebra S T] [IsScalarTower R S T] [Mo
dule.Free R S] [Module.Finite R S] [Module.Free S T] [Module.Finite S T] (x : T)
 : trace …

--- 原说明 ---
Let `T / S / R` be a tower of finite extensions of fields. Then
$\text{Trace}_{T/R} = \text{Trace}_{S/R} \circ \text{Trace}_{T/S}$.
-/
theorem trace_comp_trace [Algebra S T] [IsScalarTower R S T]
    [Module.Free R S] [Module.Finite R S] [Module.Free S T] [Module.Finite S T] :
    (trace R S).comp ((trace S T).restrictScalars R) = trace R T :=
  LinearMap.ext trace_trace

@[simp]
/-
**Algebra.trace_prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：trace_prod_apply [Module.Free R S] [Module.Free R T] [Module.Finite R S] [
Module.Finite R T] (x : S × T) : trace R (S × T) x = trace R S x.fst + trace R T
 x.snd
参数：x : S × T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext₂`：ext₂ {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (H : forall m n, 
f m n = g m n) : f = g
· 使用定理 `Prod.mul_def`：mul_def (p q : M × N) : p * q = (p.1 * q.1, p.2 * q.2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearMap.trace_prodMap'`：trace_prodMap' (f : M ->ₗ[R] M) (g : N ->ₗ[R] 
N) : trace R (M × N) (prodMap f g) = trace R M f + trace R N g
-/
theorem trace_prod_apply [Module.Free R S] [Module.Free R T] [Module.Finite R S] [Module.Finite R T]
    (x : S × T) : trace R (S × T) x = trace R S x.fst + trace R T x.snd := by
  let f := (lmul R S).toLinearMap.prodMap (lmul R T).toLinearMap
  have : (lmul R (S × T)).toLinearMap = (prodMapLinear R S T S T R).comp f :=
    LinearMap.ext₂ Prod.mul_def
  simp_rw [trace, this]
  exact trace_prodMap' _ _
/-
**Algebra.trace_prod** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：trace_prod [Module.Free R S] [Module.Free R T] [Module.Finite R S] [Module
.Finite R T] : trace R (S × T) = (trace R S).coprod (trace R T)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.coprod_apply`：coprod_apply (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃
) (x : M × M₂) : coprod f g x = f x.1 + g x.2
· 使用定理 `Algebra.trace_prod_apply`：trace_prod_apply [Module.Free R S] [Module.Fre
e R T] [Module.Finite R S] [Module.Finite R T] (x : S × T) : trace R (S × T) x =
 trace R S x.f…
-/
theorem trace_prod [Module.Free R S] [Module.Free R T] [Module.Finite R S] [Module.Finite R T] :
    trace R (S × T) = (trace R S).coprod (trace R T) :=
  LinearMap.ext fun p => by rw [coprod_apply, trace_prod_apply]

section TraceForm

variable (R S)
open LinearMap
/-- The `traceForm` maps `x y : S` to the trace of `x * y`.
It is a symmetric bilinear form and is nondegenerate if the extension is separable. -/
@[stacks 0BIK "Trace pairing"]
/-
**Algebra.traceForm** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：traceForm : BilinForm R S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `traceForm` maps `x y : S` to the trace of `x * y`.
It is a symmetric bilinear form and is nondegenerate if the extension is separab
le.
-/
noncomputable def traceForm : BilinForm R S :=
  LinearMap.compr₂ (lmul R S).toLinearMap (trace R S)

variable {S}

-- This is a nicer lemma than the one produced by `@[simps] def traceForm`.
@[simp]
/-
**Algebra.traceForm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：traceForm_apply (x y : S) : traceForm R S x y = trace R S (x * y)
参数：x y : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem traceForm_apply (x y : S) : traceForm R S x y = trace R S (x * y) :=
  rfl
/-
**Algebra.traceForm_isSymm** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：traceForm_isSymm : (traceForm R S).IsSymm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem traceForm_isSymm : (traceForm R S).IsSymm :=
  ⟨fun _ _ => congr_arg (trace R S) (mul_comm _ _)⟩
/-
**Algebra.traceForm_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：traceForm_toMatrix [DecidableEq ι] (b : Basis ι R S) (i j) : (traceForm R 
S).toMatrix b i j = trace R S (b i * b j)
参数：b : Basis ι R S；i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.toMatrix_apply`：LinearMap.BilinForm.toMatrix_apply (
B : BilinForm R₁ M₁) (i j : n) : BilinForm.toMatrix b B i j = B (b i) (b j)
· 使用定理 `Algebra.traceForm_apply`：traceForm_apply (x y : S) : traceForm R S x y =
 trace R S (x * y)
-/
theorem traceForm_toMatrix [DecidableEq ι] (b : Basis ι R S) (i j) :
    (traceForm R S).toMatrix b i j = trace R S (b i * b j) := by
  rw [LinearMap.BilinForm.toMatrix_apply, traceForm_apply]

end TraceForm

end Algebra

