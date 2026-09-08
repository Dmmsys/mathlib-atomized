/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Polynomial.SeparableDegree

/-!

# Separable degree

This file contains basics about the separable degree of a field extension.

## Main definitions

- `Field.Emb F E`: the type of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`
  (the algebraic closure of `F` is usually used in the literature, but our definition has the
  advantage that `Field.Emb F E` lies in the same universe as `E` rather than the maximum over `F`
  and `E`). Usually denoted by $\operatorname{Emb}_F(E)$ in textbooks.

- `Field.finSepDegree F E`: the (finite) separable degree $[E:F]_s$ of an extension `E / F`
  of fields, defined to be the number of `F`-algebra homomorphisms from `E` to the algebraic
  closure of `E`, as a natural number. It is zero if `Field.Emb F E` is not finite.
  Note that if `E / F` is not algebraic, then this definition makes no mathematical sense.

  **Remark:** the `Cardinal`-valued, potentially infinite separable degree `Field.sepDegree F E`
  for a general algebraic extension `E / F` is defined to be the degree of `L / F`, where `L` is
  the separable closure of `F` in `E`, which is not defined in this file yet. Later we
  will show that (`Field.finSepDegree_eq`), if `Field.Emb F E` is finite, then these two
  definitions coincide. If `E / F` is algebraic with infinite separable degree, we have
  `#(Field.Emb F E) = 2 ^ Field.sepDegree F E` instead.
  (See `Field.Emb.cardinal_eq_two_pow_sepDegree` in another file.) For example, if
  $F = \mathbb{Q}$ and $E = \mathbb{Q}( \mu_{p^\infty} )$, then $\operatorname{Emb}_F (E)$
  is in bijection with $\operatorname{Gal}(E/F)$, which is isomorphic to
  $\mathbb{Z}_p^\times$, which is uncountable, whereas $ [E:F] $ is countable.

- `Polynomial.natSepDegree`: the separable degree of a polynomial is a natural number,
  defined to be the number of distinct roots of it over its splitting field.

## Main results

- `Field.embEquivOfEquiv`, `Field.finSepDegree_eq_of_equiv`:
  a random bijection between `Field.Emb F E` and `Field.Emb F K` when `E` and `K` are isomorphic
  as `F`-algebras. In particular, they have the same cardinality (so their
  `Field.finSepDegree` are equal).

- `Field.embEquivOfAdjoinSplits`,
  `Field.finSepDegree_eq_of_adjoin_splits`: a random bijection between `Field.Emb F E` and
  `E →ₐ[F] K` if `E = F(S)` such that every element `s` of `S` is integral (= algebraic) over `F`
  and whose minimal polynomial splits in `K`. In particular, they have the same cardinality.

- `Field.embEquivOfIsAlgClosed`,
  `Field.finSepDegree_eq_of_isAlgClosed`: a random bijection between `Field.Emb F E` and
  `E →ₐ[F] K` when `E / F` is algebraic and `K / F` is algebraically closed.
  In particular, they have the same cardinality.

- `Field.embProdEmbOfIsAlgebraic`, `Field.finSepDegree_mul_finSepDegree_of_isAlgebraic`:
  if `K / E / F` is a field extension tower, such that `K / E` is algebraic,
  then there is a non-canonical bijection `Field.Emb F E × Field.Emb E K ≃ Field.Emb F K`.
  In particular, the separable degrees satisfy the tower law: $[E:F]_s [K:E]_s = [K:F]_s$
  (see also `Module.finrank_mul_finrank`).

- `Field.infinite_emb_of_transcendental`: `Field.Emb` is infinite for transcendental extensions.

- `Polynomial.natSepDegree_le_natDegree`: the separable degree of a polynomial is smaller than
  its degree.

- `Polynomial.natSepDegree_eq_natDegree_iff`: the separable degree of a non-zero polynomial is
  equal to its degree if and only if it is separable.

- `Polynomial.natSepDegree_eq_of_splits`: if a polynomial splits over `E`, then its separable degree
  is equal to the number of distinct roots of it over `E`.

- `Polynomial.natSepDegree_eq_of_isAlgClosed`: the separable degree of a polynomial is equal to
  the number of distinct roots of it over any algebraically closed field.

- `Polynomial.natSepDegree_expand`: if a field `F` is of exponential characteristic
  `q`, then `Polynomial.expand F (q ^ n) f` and `f` have the same separable degree.

- `Polynomial.HasSeparableContraction.natSepDegree_eq`: if a polynomial has separable
  contraction, then its separable degree is equal to its separable contraction degree.

- `Irreducible.natSepDegree_dvd_natDegree`: the separable degree of an irreducible
  polynomial divides its degree.

- `IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree`: the separable degree of
  `F⟮α⟯ / F` is equal to the separable degree of the minimal polynomial of `α` over `F`.

- `IntermediateField.finSepDegree_adjoin_simple_eq_finrank_iff`: if `α` is algebraic over `F`, then
  the separable degree of `F⟮α⟯ / F` is equal to the degree of `F⟮α⟯ / F` if and only if `α` is a
  separable element.

- `Field.finSepDegree_dvd_finrank`: the separable degree of any field extension `E / F` divides
  the degree of `E / F`.

- `Field.finSepDegree_le_finrank`: the separable degree of a finite extension `E / F` is smaller
  than the degree of `E / F`.

- `Field.finSepDegree_eq_finrank_iff`: if `E / F` is a finite extension, then its separable degree
  is equal to its degree if and only if it is a separable extension.

- `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`: `F⟮x⟯ / F` is a separable extension
  if and only if `x` is a separable element.

- `Algebra.IsSeparable.trans`: if `E / F` and `K / E` are both separable, then `K / F` is also
  separable.

## Tags

separable degree, degree, polynomial

-/

@[expose] public section

open Module Polynomial IntermediateField Field

noncomputable section

universe u v w

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
variable (K : Type w) [Field K] [Algebra F K]

namespace Field

/-- `Field.Emb F E` is the type of `F`-algebra homomorphisms from `E` to the algebraic closure
of `E`. -/
/-
**Field.Emb** 是 Mathlib 中的一个缩写定义，位于命名空间 `Field`。
形式化陈述：Emb
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Field.Emb F E` is the type of `F`-algebra homomorphisms from `E` to the algebra
ic closure
of `E`.
-/
abbrev Emb := E →ₐ[F] AlgebraicClosure E

/-- If `E / F` is an algebraic extension, then the (finite) separable degree of `E / F`
is the number of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`,
as a natural number. It is defined to be zero if there are infinitely many of them.
Note that if `E / F` is not algebraic, then this definition makes no mathematical sense. -/
/-
**Field.finSepDegree** 是 Mathlib 中的一个定义，位于命名空间 `Field`。
形式化陈述：finSepDegree : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E / F` is an algebraic extension, then the (finite) separable degree of `E /
 F`
is the number of `F`-algebra homomorphisms from `E` to the algebraic closure of 
`E`,
as a natural number. It is defined to be zero if there are infinitely many of th
em.
Note that if `E / F` is not algebraic, then this definition makes no mathematica
l sense.
-/
def finSepDegree : ℕ := Nat.card (Emb F E)
/-
**Field.instInhabitedEmb** 是 Mathlib 中的一个实例，位于命名空间 `Field`。
形式化陈述：instInhabitedEmb : Inhabited (Emb F E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabitedEmb : Inhabited (Emb F E) := ⟨IsScalarTower.toAlgHom F E _⟩
/-
**Field.instNeZeroFinSepDegree** 是 Mathlib 中的一个实例，位于命名空间 `Field`。
形式化陈述：instNeZeroFinSepDegree [FiniteDimensional F E] : NeZero (finSepDegree F E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.card_ne_zero`：card_ne_zero : Nat.card α != 0 ↔ Nonempty α ∧ Finite α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Fintype.finite`：∀ {α : Type u_4} (_inst : Fintype α), Finite α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
instance instNeZeroFinSepDegree [FiniteDimensional F E] : NeZero (finSepDegree F E) :=
  ⟨Nat.card_ne_zero.2 ⟨inferInstance, Fintype.finite <| minpoly.AlgHom.fintype _ _ _⟩⟩

/-- A random bijection between `Field.Emb F E` and `Field.Emb F K` when `E` and `K` are isomorphic
as `F`-algebras. -/
/-
**Field.embEquivOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Field`。
形式化陈述：embEquivOfEquiv (i : E ≃ₐ[F] K) : Emb F E ≃ Emb F K
参数：i : E ≃ₐ[F] K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A random bijection between `Field.Emb F E` and `Field.Emb F K` when `E` and `K` 
are isomorphic
as `F`-algebras.
-/
def embEquivOfEquiv (i : E ≃ₐ[F] K) :
    Emb F E ≃ Emb F K := AlgEquiv.arrowCongr i <| AlgEquiv.symm <| by
  let _ : Algebra E K := i.toAlgHom.toRingHom.toAlgebra
  have : Algebra.IsAlgebraic E K := by
    constructor
    intro x
    have h := isAlgebraic_algebraMap (R := E) (A := K) (i.symm.toAlgHom x)
    rw [show ∀ y : E, (algebraMap E K) y = i.toAlgHom y from fun y ↦ rfl] at h
    simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using h
  apply AlgEquiv.restrictScalars (R := F) (S := E)
  exact IsAlgClosure.equivOfAlgebraic E K (AlgebraicClosure K) (AlgebraicClosure E)

/-- If `E` and `K` are isomorphic as `F`-algebras, then they have the same `Field.finSepDegree`
over `F`. -/
/-
**Field.finSepDegree_eq_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：finSepDegree_eq_of_equiv (i : E ≃ₐ[F] K) : finSepDegree F E = finSepDegree
 F K
参数：i : E ≃ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β

--- 原说明 ---
If `E` and `K` are isomorphic as `F`-algebras, then they have the same `Field.fi
nSepDegree`
over `F`.
-/
theorem finSepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    finSepDegree F E = finSepDegree F K := Nat.card_congr (embEquivOfEquiv F E K i)

@[simp]
/-
**Field.finSepDegree_self** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：finSepDegree_self : finSepDegree F F = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Field.finSepDegree.eq_1`：∀ (F : Type u) (E : Type v) [inst : Field F] [i
nst_1 : Field E] [inst_2 : Algebra F E],   Field.finSepDegree F E = Nat.card (Fi
eld.Emb F E)
· 使用定理 `Nat.card_eq_one_iff_unique`：card_eq_one_iff_unique : Nat.card α = 1 ↔ Su
bsingleton α ∧ Nonempty α
· 使用定理 `AlgHom.subsingleton`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Co
mmSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring 
B] [inst_…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem finSepDegree_self : finSepDegree F F = 1 := by
  rw [finSepDegree, Nat.card_eq_one_iff_unique]
  constructor <;> infer_instance

end Field

namespace IntermediateField

@[simp]
/-
**IntermediateField.finSepDegree_bot** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：finSepDegree_bot : finSepDegree F (⊥ : IntermediateField F E) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Field.finSepDegree_eq_of_equiv`：finSepDegree_eq_of_equiv (i : E ≃ₐ[F] K)
 : finSepDegree F E = finSepDegree F K
· 使用定理 `Field.finSepDegree_self`：finSepDegree_self : finSepDegree F F = 1
-/
theorem finSepDegree_bot : finSepDegree F (⊥ : IntermediateField F E) = 1 := by
  rw [finSepDegree_eq_of_equiv _ _ _ (botEquiv F E), finSepDegree_self]

section Tower

variable {F}
variable [Algebra E K] [IsScalarTower F E K]

@[simp]
/-
**IntermediateField.finSepDegree_bot'** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：finSepDegree_bot' : finSepDegree F (⊥ : IntermediateField E K) = finSepDeg
ree F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.finSepDegree_eq_of_equiv`：finSepDegree_eq_of_equiv (i : E ≃ₐ[F] K)
 : finSepDegree F E = finSepDegree F K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem finSepDegree_bot' : finSepDegree F (⊥ : IntermediateField E K) = finSepDegree F E :=
  finSepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

@[simp]
/-
**IntermediateField.finSepDegree_top** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：finSepDegree_top : finSepDegree F (⊤ : IntermediateField E K) = finSepDegr
ee F K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.finSepDegree_eq_of_equiv`：finSepDegree_eq_of_equiv (i : E ≃ₐ[F] K)
 : finSepDegree F E = finSepDegree F K
-/
theorem finSepDegree_top : finSepDegree F (⊤ : IntermediateField E K) = finSepDegree F K :=
  finSepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)

end Tower

/-
**IntermediateField.isSeparable_bot** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField
`。
形式化陈述：isSeparable_bot : Algebra.IsSeparable F (⊥ : IntermediateField F E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.Algebra.isSeparable`：AlgEquiv.Algebra.isSeparable [Algebra.IsSe
parable F K] : Algebra.IsSeparable F E
-/
theorem isSeparable_bot : Algebra.IsSeparable F (⊥ : IntermediateField F E) :=
  AlgEquiv.Algebra.isSeparable (IntermediateField.botEquiv F E).symm
/-
**IntermediateField.isSeparable_top** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField
`。
形式化陈述：isSeparable_top : Algebra.IsSeparable F (⊤ : IntermediateField F E) ↔ Alge
bra.IsSeparable F E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.IsSeparable.iff_of_equiv_equiv`：Algebra.IsSeparable.iff_of_equiv
_equiv : Algebra.IsSeparable A₁ B₁ ↔ Algebra.IsSeparable A₂ B₂
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isSeparable_top :
    Algebra.IsSeparable F (⊤ : IntermediateField F E) ↔ Algebra.IsSeparable F E :=
  Algebra.IsSeparable.iff_of_equiv_equiv (RingEquiv.refl F) topEquiv.toRingEquiv (by ext; simp)

end IntermediateField

namespace Field

/-- A random bijection between `Field.Emb F E` and `E →ₐ[F] K` if `E = F(S)` such that every
element `s` of `S` is integral (= algebraic) over `F` and whose minimal polynomial splits in `K`.
Combined with `Field.instInhabitedEmb`, it can be viewed as a stronger version of
`IntermediateField.nonempty_algHom_of_adjoin_splits`. -/
/-
**Field.embEquivOfAdjoinSplits** 是 Mathlib 中的一个定义，位于命名空间 `Field`。
形式化陈述：embEquivOfAdjoinSplits {S : Set E} (hS : adjoin F S = ⊤) (hK : forall s in
 S, IsIntegral F s ∧ Splits ((minpoly F s).map (algebraMap F K))) : Emb F E ≃ (E
 ->ₐ[F] K)
参数：hS : adjoin F S = ⊤；hK : forall s in S, IsIntegral F s ∧ Splits ((minpoly F s
).map (algebraMap F K))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A random bijection between `Field.Emb F E` and `E →ₐ[F] K` if `E = F(S)` such th
at every
element `s` of `S` is integral (= algebraic) over `F` and whose minimal polynomi
al splits in `K`.
Combined with `Field.instInhabitedEmb`, it can be viewed as a stronger version o
f
`IntermediateField.nonempty_algHom_of_adjoin_splits`.
-/
def embEquivOfAdjoinSplits {S : Set E} (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Splits ((minpoly F s).map (algebraMap F K))) :
    Emb F E ≃ (E →ₐ[F] K) :=
  have : Algebra.IsAlgebraic F (⊤ : IntermediateField F E) :=
    (hS ▸ isAlgebraic_adjoin (S := S) fun x hx ↦ (hK x hx).1)
  have halg := (topEquiv (F := F) (E := E)).isAlgebraic
  Classical.choice <| Function.Embedding.antisymm
    (halg.algHomEmbeddingOfSplits (fun _ ↦ splits_of_mem_adjoin F E (S := S) hK (hS ▸ mem_top)) _)
    (halg.algHomEmbeddingOfSplits (fun _ ↦ IsAlgClosed.splits _) _)

/-- The `Field.finSepDegree F E` is equal to the cardinality of `E →ₐ[F] K`
if `E = F(S)` such that every element
`s` of `S` is integral (= algebraic) over `F` and whose minimal polynomial splits in `K`. -/
/-
**Field.finSepDegree_eq_of_adjoin_splits** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：finSepDegree_eq_of_adjoin_splits {S : Set E} (hS : adjoin F S = ⊤) (hK : f
orall s in S, IsIntegral F s ∧ Splits ((minpoly F s).map (algebraMap F K))) : fi
nSepDegree F E = Nat.card (E ->ₐ[F] K)
参数：hS : adjoin F S = ⊤；hK : forall s in S, IsIntegral F s ∧ Splits ((minpoly F s
).map (algebraMap F K))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β

--- 原说明 ---
The `Field.finSepDegree F E` is equal to the cardinality of `E →ₐ[F] K`
if `E = F(S)` such that every element
`s` of `S` is integral (= algebraic) over `F` and whose minimal polynomial split
s in `K`.
-/
theorem finSepDegree_eq_of_adjoin_splits {S : Set E} (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Splits ((minpoly F s).map (algebraMap F K))) :
    finSepDegree F E = Nat.card (E →ₐ[F] K) := Nat.card_congr (embEquivOfAdjoinSplits F E K hS hK)

/-- A random bijection between `Field.Emb F E` and `E →ₐ[F] K` when `E / F` is algebraic
and `K / F` is algebraically closed. -/
/-
**Field.embEquivOfIsAlgClosed** 是 Mathlib 中的一个定义，位于命名空间 `Field`。
形式化陈述：embEquivOfIsAlgClosed [Algebra.IsAlgebraic F E] [IsAlgClosed K] : Emb F E 
≃ (E ->ₐ[F] K)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_univ`：adjoin_univ (F E : Type*) [Field F] [Fiel
d E] [Algebra F E] : adjoin F (Set.univ : Set E) = ⊤

--- 原说明 ---
A random bijection between `Field.Emb F E` and `E →ₐ[F] K` when `E / F` is algeb
raic
and `K / F` is algebraically closed.
-/
def embEquivOfIsAlgClosed [Algebra.IsAlgebraic F E] [IsAlgClosed K] :
    Emb F E ≃ (E →ₐ[F] K) :=
  embEquivOfAdjoinSplits F E K (adjoin_univ F E) fun s _ ↦
    ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩

/-- The `Field.finSepDegree F E` is equal to the cardinality of `E →ₐ[F] K` as a natural number,
when `E / F` is algebraic and `K / F` is algebraically closed. -/
@[stacks 09HJ "We use `finSepDegree` to state a more general result."]
/-
**Field.finSepDegree_eq_of_isAlgClosed** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：finSepDegree_eq_of_isAlgClosed [Algebra.IsAlgebraic F E] [IsAlgClosed K] :
 finSepDegree F E = Nat.card (E ->ₐ[F] K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β

--- 原说明 ---
The `Field.finSepDegree F E` is equal to the cardinality of `E →ₐ[F] K` as a nat
ural number,
when `E / F` is algebraic and `K / F` is algebraically closed.
-/
theorem finSepDegree_eq_of_isAlgClosed [Algebra.IsAlgebraic F E] [IsAlgClosed K] :
    finSepDegree F E = Nat.card (E →ₐ[F] K) := Nat.card_congr (embEquivOfIsAlgClosed F E K)

/-- If `K / E / F` is a field extension tower, such that `K / E` is algebraic,
then there is a non-canonical bijection
`Field.Emb F E × Field.Emb E K ≃ Field.Emb F K`. A corollary of `algHomEquivSigma`. -/
/-
**Field.embProdEmbOfIsAlgebraic** 是 Mathlib 中的一个定义，位于命名空间 `Field`。
形式化陈述：embProdEmbOfIsAlgebraic [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlg
ebraic E K] : Emb F E × Emb E K ≃ Emb F K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `K / E` is algebraic,
then there is a non-canonical bijection
`Field.Emb F E × Field.Emb E K ≃ Field.Emb F K`. A corollary of `algHomEquivSigm
a`.
-/
def embProdEmbOfIsAlgebraic [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebraic E K] :
    Emb F E × Emb E K ≃ Emb F K :=
  let e : ∀ f : E →ₐ[F] AlgebraicClosure K,
      @AlgHom E K _ _ _ _ _ f.toRingHom.toAlgebra ≃ Emb E K := fun f ↦
    (@embEquivOfIsAlgClosed E K _ _ _ _ _ f.toRingHom.toAlgebra).symm
  (algHomEquivSigma (A := F) (B := E) (C := K) (D := AlgebraicClosure K) |>.trans
    (Equiv.sigmaEquivProdOfEquiv e) |>.trans <| Equiv.prodCongrLeft <|
      fun _ : Emb E K ↦ AlgEquiv.arrowCongr (@AlgEquiv.refl F E _ _ _) <|
        (IsAlgClosure.equivOfAlgebraic E K (AlgebraicClosure K)
          (AlgebraicClosure E)).restrictScalars F).symm

/-- If the field extension `E / F` is transcendental, then `Field.Emb F E` is infinite. -/
/-
**Field.infinite_emb_of_transcendental** 是 Mathlib 中的一个实例，位于命名空间 `Field`。
形式化陈述：infinite_emb_of_transcendental [H : Algebra.Transcendental F E] : Infinite
 (Emb F E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_isTranscendenceBasis'`：exists_isTranscendenceBasis' [FaithfulSMul
 R A] : exists (ι : Type w) (x : ι -> A), IsTranscendenceBasis R x
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsTranscendenceBasis.isAlgebraic_field`：IsTranscendenceBasis.isAlgebraic
_field {F E : Type*} {x : ι -> E} [Field F] [Field E] [Algebra F E] (hx : IsTran
scendenceBasis F x) : Algebr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.infinite_iff`：Equiv.infinite_iff (e : α ≃ β) : Infinite α ↔ Infini
te β
· 使用定理 `MvPolynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} {σ : Type u_1} [i
nst : CommSemiring R] [IsCancelAdd R] [IsDomain R], IsDomain (MvPolynomial σ R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsTranscendenceBasis.nonempty_iff_transcendental`：IsTranscendenceBasis.n
onempty_iff_transcendental [Nontrivial R] (hx : IsTranscendenceBasis R x) : None
mpty ι ↔ Algebra.Transcendental R A
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.coe_toAlgHom'`：coe_toAlgHom' : (toAlgHom R S A : S -> A) =
 algebraMap S A
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `MvPolynomial.instNoZeroDivisors`：∀ {R : Type u} {σ : Type u_1} [inst : C
ommSemiring R] [NoZeroDivisors R], NoZeroDivisors (MvPolynomial σ R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
If the field extension `E / F` is transcendental, then `Field.Emb F E` is infini
te.
-/
instance infinite_emb_of_transcendental [H : Algebra.Transcendental F E] : Infinite (Emb F E) := by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' F E
  have := hx.isAlgebraic_field
  rw [← (embProdEmbOfIsAlgebraic F (adjoin F (Set.range x)) E).infinite_iff]
  refine @Prod.infinite_of_left _ _ ?_ _
  rw [← (embEquivOfEquiv _ _ _ hx.1.aevalEquivField).infinite_iff]
  obtain ⟨i⟩ := hx.nonempty_iff_transcendental.2 H
  let K := FractionRing (MvPolynomial ι F)
  let i1 := IsScalarTower.toAlgHom F (MvPolynomial ι F) (AlgebraicClosure K)
  have hi1 : Function.Injective i1 := by
    rw [IsScalarTower.coe_toAlgHom', IsScalarTower.algebraMap_eq _ K]
    exact (algebraMap K (AlgebraicClosure K)).injective.comp (IsFractionRing.injective _ _)
  let f (n : ℕ) : Emb F K := IsFractionRing.liftAlgHom
    (g := i1.comp <| MvPolynomial.aeval fun i : ι ↦ MvPolynomial.X i ^ (n + 1)) <| hi1.comp <| by
      simpa [algebraicIndependent_iff_injective_aeval] using
        MvPolynomial.algebraicIndependent_polynomial_aeval_X _
          fun i : ι ↦ (Polynomial.transcendental_X F).pow n.succ_pos
  refine Infinite.of_injective f fun m n h ↦ ?_
  replace h : (MvPolynomial.X i) ^ (m + 1) = (MvPolynomial.X i) ^ (n + 1) := hi1 <| by
    simpa [f, -map_pow] using congr($h (algebraMap _ K (MvPolynomial.X (R := F) i)))
  simpa using congr(MvPolynomial.totalDegree $h)

/-- If the field extension `E / F` is transcendental, then `Field.finSepDegree F E = 0`, which
actually means that `Field.Emb F E` is infinite (see `Field.infinite_emb_of_transcendental`). -/
/-
**Field.finSepDegree_eq_zero_of_transcendental** 是 Mathlib 中的一个定理，位于命名空间 `Field`
。
形式化陈述：finSepDegree_eq_zero_of_transcendental [Algebra.Transcendental F E] : finS
epDegree F E = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0

--- 原说明 ---
If the field extension `E / F` is transcendental, then `Field.finSepDegree F E =
 0`, which
actually means that `Field.Emb F E` is infinite (see `Field.infinite_emb_of_tran
scendental`).
-/
theorem finSepDegree_eq_zero_of_transcendental [Algebra.Transcendental F E] :
    finSepDegree F E = 0 := Nat.card_eq_zero_of_infinite

/-- If `K / E / F` is a field extension tower, such that `K / E` is algebraic, then their
separable degrees satisfy the tower law
$[E:F]_s [K:E]_s = [K:F]_s$. See also `Module.finrank_mul_finrank`. -/
@[stacks 09HK "Part 1, `finSepDegree` variant"]
/-
**Field.finSepDegree_mul_finSepDegree_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 `
Field`。
形式化陈述：finSepDegree_mul_finSepDegree_of_isAlgebraic [Algebra E K] [IsScalarTower 
F E K] [Algebra.IsAlgebraic E K] : finSepDegree F E * finSepDegree E K = finSepD
egree F K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `K / E` is algebraic, then 
their
separable degrees satisfy the tower law
$[E:F]_s [K:E]_s = [K:F]_s$. See also `Module.finrank_mul_finrank`.
-/
theorem finSepDegree_mul_finSepDegree_of_isAlgebraic
    [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebraic E K] :
    finSepDegree F E * finSepDegree E K = finSepDegree F K := by
  simpa only [Nat.card_prod] using! Nat.card_congr (embProdEmbOfIsAlgebraic F E K)

end Field

namespace Polynomial

variable {F E}
variable (f : F[X])

open scoped Classical in
/-- The separable degree `Polynomial.natSepDegree` of a polynomial is a natural number,
defined to be the number of distinct roots of it over its splitting field.
This is similar to `Polynomial.natDegree` but not to `Polynomial.degree`, namely, the separable
degree of `0` is `0`, not negative infinity. -/
/-
**Polynomial.natSepDegree** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The separable degree `Polynomial.natSepDegree` of a polynomial is a natural numb
er,
defined to be the number of distinct roots of it over its splitting field.
This is similar to `Polynomial.natDegree` but not to `Polynomial.degree`, namely
, the separable
degree of `0` is `0`, not negative infinity.
-/
def natSepDegree : ℕ := (f.aroots f.SplittingField).toFinset.card

/-- The separable degree of a polynomial is smaller than its degree. -/
/-
**Polynomial.natSepDegree_le_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_le_natDegree : f.natSepDegree <= f.natDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.card_roots'`：card_roots' (p : R[X]) : Multiset.card p.roots <
= natDegree p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Multiset.toFinset_card_le`：Multiset.toFinset_card_le : #m.toFinset <= Mu
ltiset.card m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_map`：natDegree_map (f : R ->+* S) : (p.map f).natDe
gree = p.natDegree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aroots_def`：aroots_def (p : T[X]) (S) [CommRing S] [IsDomain 
S] [Algebra T S] : p.aroots S = (p.map (algebraMap T S)).roots

--- 原说明 ---
The separable degree of a polynomial is smaller than its degree.
-/
theorem natSepDegree_le_natDegree : f.natSepDegree ≤ f.natDegree := by
  have := f.map (algebraMap F f.SplittingField) |>.card_roots'
  rw [← aroots_def, natDegree_map] at this
  classical
  exact (f.aroots f.SplittingField).toFinset_card_le.trans this

@[simp]
/-
**Polynomial.natSepDegree_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_X_sub_C (x : F) : (X - C x).natSepDegree = 1
参数：x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aroots_X_sub_C`：aroots_X_sub_C [CommRing S] [IsDomain S] [Alg
ebra T S] (r : T) : aroots (X - C r) S = {algebraMap T S r}
· 使用定理 `Multiset.toFinset_singleton`：toFinset_singleton (a : α) : toFinset ({a} 
: Multiset α) = {a}
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natSepDegree_X_sub_C (x : F) : (X - C x).natSepDegree = 1 := by
  simp only [natSepDegree, aroots_X_sub_C, Multiset.toFinset_singleton, Finset.card_singleton]

@[simp]
/-
**Polynomial.natSepDegree_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_X : (X : F[X]).natSepDegree = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aroots_X`：aroots_X [CommRing S] [IsDomain S] [Algebra T S] : 
aroots (X : T[X]) S = {0}
· 使用定理 `Multiset.toFinset_singleton`：toFinset_singleton (a : α) : toFinset ({a} 
: Multiset α) = {a}
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natSepDegree_X : (X : F[X]).natSepDegree = 1 := by
  simp only [natSepDegree, aroots_X, Multiset.toFinset_singleton, Finset.card_singleton]

/-- A constant polynomial has zero separable degree. -/
/-
**Polynomial.natSepDegree_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_eq_zero (h : f.natDegree = 0) : f.natSepDegree = 0
参数：h : f.natDegree = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
A constant polynomial has zero separable degree.
-/
theorem natSepDegree_eq_zero (h : f.natDegree = 0) : f.natSepDegree = 0 := by
  linarith only [natSepDegree_le_natDegree f, h]

@[simp]
/-
**Polynomial.natSepDegree_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_C (x : F) : (C x).natSepDegree = 0
参数：x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natSepDegree_eq_zero`：natSepDegree_eq_zero (h : f.natDegree =
 0) : f.natSepDegree = 0
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
-/
theorem natSepDegree_C (x : F) : (C x).natSepDegree = 0 := natSepDegree_eq_zero _ (natDegree_C _)

@[simp]
/-
**Polynomial.natSepDegree_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_zero : (0 : F[X]).natSepDegree = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `Polynomial.natSepDegree_C`：natSepDegree_C (x : F) : (C x).natSepDegree =
 0
-/
theorem natSepDegree_zero : (0 : F[X]).natSepDegree = 0 := by
  rw [← C_0, natSepDegree_C]

@[simp]
/-
**Polynomial.natSepDegree_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_one : (1 : F[X]).natSepDegree = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.natSepDegree_C`：natSepDegree_C (x : F) : (C x).natSepDegree =
 0
-/
theorem natSepDegree_one : (1 : F[X]).natSepDegree = 0 := by
  rw [← C_1, natSepDegree_C]

/-- A non-constant polynomial has non-zero separable degree. -/
/-
**Polynomial.natSepDegree_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_ne_zero (h : f.natDegree != 0) : f.natSepDegree != 0
参数：h : f.natDegree != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natSepDegree.eq_1`：∀ {F : Type u} [inst : Field F] (f : Polyn
omial F), f.natSepDegree = (f.aroots f.SplittingField).toFinset.card
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `Polynomial.SplittingField.splits`：∀ {K : Type v} [inst : Field K] (f : P
olynomial K), (Polynomial.map (algebraMap K f.SplittingField) f).Splits
· 使用定理 `Polynomial.degree_ne_of_natDegree_ne`：degree_ne_of_natDegree_ne {n : Nat
} : p.natDegree != n -> degree p != n
· 使用定理 `Polynomial.natDegree_map`：natDegree_map (f : R ->+* S) : (p.map f).natDe
gree = p.natDegree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Polynomial.mem_aroots`：mem_aroots [IsDomain T] [CommRing S] [IsDomain S]
 [Algebra T S] [Module.IsTorsionFree T S] {p : T[X]} {a : S} : a in p.aroots S ↔
 p != 0 ∧ a…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.IsSplittingField.instIsTorsionFreeSplittingField`：∀ {K : Type
 v} [inst : Field K] (f : Polynomial K), Module.IsTorsionFree K f.SplittingField
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_rootOfSplits`：eval_rootOfSplits (hf : f.Splits) (hfd : f
.degree != 0) : f.eval (rootOfSplits hf hfd) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A non-constant polynomial has non-zero separable degree.
-/
theorem natSepDegree_ne_zero (h : f.natDegree ≠ 0) : f.natSepDegree ≠ 0 := by
  rw [natSepDegree, ne_eq, Finset.card_eq_zero, ← ne_eq, ← Finset.nonempty_iff_ne_empty]
  use rootOfSplits (SplittingField.splits f) (degree_ne_of_natDegree_ne (by rwa [natDegree_map]))
  classical
  rw [Multiset.mem_toFinset, mem_aroots]
  exact ⟨ne_of_apply_ne _ h, by simp only [← eval_map_algebraMap, eval_rootOfSplits]⟩

/-- A polynomial has zero separable degree if and only if it is constant. -/
/-
**Polynomial.natSepDegree_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_eq_zero_iff : f.natSepDegree = 0 ↔ f.natDegree = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.mtr`：∀ {a b : Prop}, (¬a → ¬b) → b → a
· 使用定理 `Polynomial.natSepDegree_ne_zero`：natSepDegree_ne_zero (h : f.natDegree !
= 0) : f.natSepDegree != 0
· 使用定理 `Polynomial.natSepDegree_eq_zero`：natSepDegree_eq_zero (h : f.natDegree =
 0) : f.natSepDegree = 0

--- 原说明 ---
A polynomial has zero separable degree if and only if it is constant.
-/
theorem natSepDegree_eq_zero_iff : f.natSepDegree = 0 ↔ f.natDegree = 0 :=
  ⟨(natSepDegree_ne_zero f).mtr, natSepDegree_eq_zero f⟩

/-- A polynomial has non-zero separable degree if and only if it is non-constant. -/
/-
**Polynomial.natSepDegree_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_ne_zero_iff : f.natSepDegree != 0 ↔ f.natDegree != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.natSepDegree_eq_zero_iff`：natSepDegree_eq_zero_iff : f.natSep
Degree = 0 ↔ f.natDegree = 0

--- 原说明 ---
A polynomial has non-zero separable degree if and only if it is non-constant.
-/
theorem natSepDegree_ne_zero_iff : f.natSepDegree ≠ 0 ↔ f.natDegree ≠ 0 :=
  Iff.not <| natSepDegree_eq_zero_iff f

/-- The separable degree of a non-zero polynomial is equal to its degree if and only if
it is separable. -/
/-
**Polynomial.natSepDegree_eq_natDegree_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：natSepDegree_eq_natDegree_iff (hf : f != 0) : f.natSepDegree = f.natDegree
 ↔ f.Separable
参数：hf : f != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.card_rootSet_eq_natDegree_iff_of_splits`：card_rootSet_eq_natD
egree_iff_of_splits [Algebra F K] {f : F[X]} (hf : f != 0) (h : (f.map (algebraM
ap F K)).Splits) : Fintype.card (f.rootS…
· 使用定理 `Polynomial.SplittingField.splits`：∀ {K : Type v} [inst : Field K] (f : P
olynomial K), (Polynomial.map (algebraMap K f.SplittingField) f).Splits
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `Polynomial.rootSet_def`：rootSet_def (p : T[X]) (S) [CommRing S] [IsDomai
n S] [Algebra T S] [DecidableEq S] : p.rootSet S = (p.aroots S).toFinset
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The separable degree of a non-zero polynomial is equal to its degree if and only
 if
it is separable.
-/
theorem natSepDegree_eq_natDegree_iff (hf : f ≠ 0) :
    f.natSepDegree = f.natDegree ↔ f.Separable := by
  classical
  simp_rw [← card_rootSet_eq_natDegree_iff_of_splits hf (SplittingField.splits f),
    rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rfl

/-- If a polynomial is separable, then its separable degree is equal to its degree. -/
/-
**Polynomial.natSepDegree_eq_natDegree_of_separable** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：natSepDegree_eq_natDegree_of_separable (h : f.Separable) : f.natSepDegree 
= f.natDegree
参数：h : f.Separable。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natSepDegree_eq_natDegree_iff`：natSepDegree_eq_natDegree_iff 
(hf : f != 0) : f.natSepDegree = f.natDegree ↔ f.Separable
· 使用定理 `Polynomial.Separable.ne_zero`：∀ {R : Type u} [inst : CommSemiring R] [No
ntrivial R] {f : Polynomial R}, f.Separable → f ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
If a polynomial is separable, then its separable degree is equal to its degree.
-/
theorem natSepDegree_eq_natDegree_of_separable (h : f.Separable) :
    f.natSepDegree = f.natDegree := (natSepDegree_eq_natDegree_iff f h.ne_zero).2 h

variable {f} in
/-- Same as `Polynomial.natSepDegree_eq_natDegree_of_separable`, but enables the use of
dot notation. -/
/-
**Polynomial.Separable.natSepDegree_eq_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial.Separable`。
形式化陈述：∀ {F : Type u} [inst : Field F] {f : Polynomial F}, f.Separable → f.natSep
Degree = f.natDegree
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natSepDegree_eq_natDegree_of_separable`：natSepDegree_eq_natDe
gree_of_separable (h : f.Separable) : f.natSepDegree = f.natDegree

--- 原说明 ---
Same as `Polynomial.natSepDegree_eq_natDegree_of_separable`, but enables the use
 of
dot notation.
-/
theorem Separable.natSepDegree_eq_natDegree (h : f.Separable) :
    f.natSepDegree = f.natDegree := natSepDegree_eq_natDegree_of_separable f h

/-- If a polynomial splits over `E`, then its separable degree is equal to
the number of distinct roots of it over `E`. -/
/-
**Polynomial.natSepDegree_eq_of_splits** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_eq_of_splits [DecidableEq E] (h : (f.map (algebraMap F E)).Sp
lits) : f.natSepDegree = (f.aroots E).toFinset.card
参数：h : (f.map (algebraMap F E)).Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aroots.eq_1`：∀ {T : Type w} [inst : CommRing T] (p : Polynomi
al T) (S : Type u_1) [inst_1 : CommRing S] [inst_2 : IsDomain S]   [inst_3 : Alg
ebra T S], p…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.Splits.roots_map`：∀ {R : Type u_1} {S : Type u_2} [inst : Fie
ld R] [inst_1 : CommRing S] [inst_2 : IsDomain S] {f : Polynomial R},   f.Splits
 → ∀ (i : R →+* S…
· 使用定理 `Polynomial.SplittingField.splits`：∀ {K : Type v} [inst : Field K] (f : P
olynomial K), (Polynomial.map (algebraMap K f.SplittingField) f).Splits
· 使用定理 `Multiset.toFinset_map`：Multiset.toFinset_map [DecidableEq α] [DecidableE
q β] (f : α -> β) (m : Multiset α) : (m.map f).toFinset = m.toFinset.image f
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.natSepDegree.eq_1`：∀ {F : Type u} [inst : Field F] (f : Polyn
omial F), f.natSepDegree = (f.aroots f.SplittingField).toFinset.card

--- 原说明 ---
If a polynomial splits over `E`, then its separable degree is equal to
the number of distinct roots of it over `E`.
-/
theorem natSepDegree_eq_of_splits [DecidableEq E] (h : (f.map (algebraMap F E)).Splits) :
    f.natSepDegree = (f.aroots E).toFinset.card := by
  classical
  rw [aroots, ← (SplittingField.lift f h).comp_algebraMap, ← map_map,
    (SplittingField.splits f).roots_map,
    Multiset.toFinset_map, Finset.card_image_of_injective _ (RingHom.injective _), natSepDegree]

variable (E) in
/-- The separable degree of a polynomial is equal to
the number of distinct roots of it over any algebraically closed field. -/
/-
**Polynomial.natSepDegree_eq_of_isAlgClosed** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：natSepDegree_eq_of_isAlgClosed [DecidableEq E] [IsAlgClosed E] : f.natSepD
egree = (f.aroots E).toFinset.card
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natSepDegree_eq_of_splits`：natSepDegree_eq_of_splits [Decidab
leEq E] (h : (f.map (algebraMap F E)).Splits) : f.natSepDegree = (f.aroots E).to
Finset.card
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits

--- 原说明 ---
The separable degree of a polynomial is equal to
the number of distinct roots of it over any algebraically closed field.
-/
theorem natSepDegree_eq_of_isAlgClosed [DecidableEq E] [IsAlgClosed E] :
    f.natSepDegree = (f.aroots E).toFinset.card :=
  natSepDegree_eq_of_splits f (IsAlgClosed.splits _)
/-
**Polynomial.natSepDegree_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_map (f : E[X]) (i : E ->+* K) : (f.map i).natSepDegree = f.na
tSepDegree
参数：f : E[X]；i : E ->+* K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.natSepDegree_eq_of_isAlgClosed`：natSepDegree_eq_of_isAlgClose
d [DecidableEq E] [IsAlgClosed E] : f.natSepDegree = (f.aroots E).toFinset.card
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natSepDegree_map (f : E[X]) (i : E →+* K) : (f.map i).natSepDegree = f.natSepDegree := by
  classical
  let _ := i.toAlgebra
  simp_rw [show i = algebraMap E K by rfl, natSepDegree_eq_of_isAlgClosed (AlgebraicClosure K),
    aroots_def, map_map, ← IsScalarTower.algebraMap_eq]

@[simp]
/-
**Polynomial.natSepDegree_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_C_mul {x : F} (hx : x != 0) : (C x * f).natSepDegree = f.natS
epDegree
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natSepDegree_eq_of_isAlgClosed`：natSepDegree_eq_of_isAlgClose
d [DecidableEq E] [IsAlgClosed E] : f.natSepDegree = (f.aroots E).toFinset.card
· 使用定理 `Polynomial.aroots_C_mul`：aroots_C_mul [IsDomain T] [CommRing S] [IsDomai
n S] [Algebra T S] [Module.IsTorsionFree T S] {a : T} (p : T[X]) (ha : a != 0) :
 (C a * p).ar…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natSepDegree_C_mul {x : F} (hx : x ≠ 0) :
    (C x * f).natSepDegree = f.natSepDegree := by
  classical
  simp only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_C_mul _ hx]

@[simp]
/-
**Polynomial.natSepDegree_smul_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_smul_nonzero {x : F} (hx : x != 0) : (x • f).natSepDegree = f
.natSepDegree
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natSepDegree_eq_of_isAlgClosed`：natSepDegree_eq_of_isAlgClose
d [DecidableEq E] [IsAlgClosed E] : f.natSepDegree = (f.aroots E).toFinset.card
· 使用定理 `Polynomial.aroots_smul_nonzero`：aroots_smul_nonzero [IsDomain T] [CommRi
ng S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] {a : T} (p : T[X]) (
ha : a != 0) : (a • …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natSepDegree_smul_nonzero {x : F} (hx : x ≠ 0) :
    (x • f).natSepDegree = f.natSepDegree := by
  classical
  simp only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_smul_nonzero _ hx]

@[simp]
/-
**Polynomial.natSepDegree_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_pow {n : Nat} : (f ^ n).natSepDegree = if n = 0 then 0 else f
.natSepDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.natSepDegree_eq_of_isAlgClosed`：natSepDegree_eq_of_isAlgClose
d [DecidableEq E] [IsAlgClosed E] : f.natSepDegree = (f.aroots E).toFinset.card
· 使用定理 `Polynomial.aroots_pow`：aroots_pow [CommRing S] [IsDomain S] [Algebra T S
] (p : T[X]) (n : Nat) : (p ^ n).aroots S = n • p.aroots S
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.toFinset_nsmul`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Mu
ltiset α) (n : ℕ), n ≠ 0 → (n • s).toFinset = s.toFinset
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem natSepDegree_pow {n : ℕ} : (f ^ n).natSepDegree = if n = 0 then 0 else f.natSepDegree := by
  classical
  simp only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_pow]
  by_cases h : n = 0
  · simp only [h, zero_smul, Multiset.toFinset_zero, Finset.card_empty, ite_true]
  simp only [h, Multiset.toFinset_nsmul _ n h, ite_false]
/-
**Polynomial.natSepDegree_pow_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_pow_of_ne_zero {n : Nat} (hn : n != 0) : (f ^ n).natSepDegree
 = f.natSepDegree
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natSepDegree_pow`：natSepDegree_pow {n : Nat} : (f ^ n).natSep
Degree = if n = 0 then 0 else f.natSepDegree
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natSepDegree_pow_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (f ^ n).natSepDegree = f.natSepDegree := by simp_rw [natSepDegree_pow, hn, ite_false]
/-
**Polynomial.natSepDegree_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_X_pow {n : Nat} : (X ^ n : F[X]).natSepDegree = if n = 0 then
 0 else 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natSepDegree_pow`：natSepDegree_pow {n : Nat} : (f ^ n).natSep
Degree = if n = 0 then 0 else f.natSepDegree
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Polynomial.natSepDegree_X`：natSepDegree_X : (X : F[X]).natSepDegree = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natSepDegree_X_pow {n : ℕ} : (X ^ n : F[X]).natSepDegree = if n = 0 then 0 else 1 := by
  simp only [natSepDegree_pow, natSepDegree_X]
/-
**Polynomial.natSepDegree_X_sub_C_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_X_sub_C_pow {x : F} {n : Nat} : ((X - C x) ^ n).natSepDegree 
= if n = 0 then 0 else 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natSepDegree_pow`：natSepDegree_pow {n : Nat} : (f ^ n).natSep
Degree = if n = 0 then 0 else f.natSepDegree
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Polynomial.natSepDegree_X_sub_C`：natSepDegree_X_sub_C (x : F) : (X - C x
).natSepDegree = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natSepDegree_X_sub_C_pow {x : F} {n : ℕ} :
    ((X - C x) ^ n).natSepDegree = if n = 0 then 0 else 1 := by
  simp only [natSepDegree_pow, natSepDegree_X_sub_C]
/-
**Polynomial.natSepDegree_C_mul_X_sub_C_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：natSepDegree_C_mul_X_sub_C_pow {x y : F} {n : Nat} (hx : x != 0) : (C x * 
(X - C y) ^ n).natSepDegree = if n = 0 then 0 else 1
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natSepDegree_C_mul`：natSepDegree_C_mul {x : F} (hx : x != 0) 
: (C x * f).natSepDegree = f.natSepDegree
· 使用定理 `Polynomial.natSepDegree_X_sub_C_pow`：natSepDegree_X_sub_C_pow {x : F} {n
 : Nat} : ((X - C x) ^ n).natSepDegree = if n = 0 then 0 else 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natSepDegree_C_mul_X_sub_C_pow {x y : F} {n : ℕ} (hx : x ≠ 0) :
    (C x * (X - C y) ^ n).natSepDegree = if n = 0 then 0 else 1 := by
  simp only [natSepDegree_C_mul _ hx, natSepDegree_X_sub_C_pow]
/-
**Polynomial.natSepDegree_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_mul (g : F[X]) : (f * g).natSepDegree <= f.natSepDegree + g.n
atSepDegree
参数：g : F[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natSepDegree_zero`：natSepDegree_zero : (0 : F[X]).natSepDegre
e = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.natSepDegree_eq_of_isAlgClosed`：natSepDegree_eq_of_isAlgClose
d [DecidableEq E] [IsAlgClosed E] : f.natSepDegree = (f.aroots E).toFinset.card
· 使用定理 `Polynomial.aroots_mul`：aroots_mul [IsDomain T] [CommRing S] [IsDomain S]
 [Algebra T S] [Module.IsTorsionFree T S] {p q : T[X]} (hpq : p * q != 0) : (p *
 q).aroots …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Multiset.toFinset_add`：toFinset_add (s t : Multiset α) : (s + t).toFinse
t = s.toFinset union t.toFinset
· 使用定理 `Finset.card_union_le`：card_union_le (s t : Finset α) : #(s union t) <= #
s + #t
-/
theorem natSepDegree_mul (g : F[X]) :
    (f * g).natSepDegree ≤ f.natSepDegree + g.natSepDegree := by
  by_cases h : f * g = 0
  · simp only [h, natSepDegree_zero, zero_le]
  classical
  simp_rw [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_mul h, Multiset.toFinset_add]
  exact Finset.card_union_le _ _
/-
**Polynomial.natSepDegree_mul_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_mul_eq_iff (g : F[X]) : (f * g).natSepDegree = f.natSepDegree
 + g.natSepDegree ↔ (f = 0 ∧ g = 0) ∨ IsCoprime f g
参数：g : F[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.natSepDegree_zero`：natSepDegree_zero : (0 : F[X]).natSepDegre
e = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `isCoprime_zero_left`：isCoprime_zero_left : IsCoprime 0 x ↔ IsUnit x
· 使用引理 `Polynomial.isUnit_iff`：isUnit_iff : IsUnit p ↔ exists r : R, IsUnit r ∧ 
C r = p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Polynomial.natSepDegree_eq_zero_iff`：natSepDegree_eq_zero_iff : f.natSep
Degree = 0 ↔ f.natDegree = 0
· 使用引理 `Polynomial.natDegree_eq_zero`：natDegree_eq_zero {p : R[X]} : p.natDegree
 = 0 ↔ exists x, C x = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.natSepDegree_eq_of_isAlgClosed`：natSepDegree_eq_of_isAlgClose
d [DecidableEq E] [IsAlgClosed E] : f.natSepDegree = (f.aroots E).toFinset.card
· 使用定理 `Polynomial.aroots_mul`：aroots_mul [IsDomain T] [CommRing S] [IsDomain S]
 [Algebra T S] [Module.IsTorsionFree T S] {p q : T[X]} (hpq : p * q != 0) : (p *
 q).aroots …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Multiset.toFinset_add`：toFinset_add (s t : Multiset α) : (s + t).toFinse
t = s.toFinset union t.toFinset
（共 61 条，此处仅展示前 30 条）
-/
theorem natSepDegree_mul_eq_iff (g : F[X]) :
    (f * g).natSepDegree = f.natSepDegree + g.natSepDegree ↔ (f = 0 ∧ g = 0) ∨ IsCoprime f g := by
  by_cases h : f * g = 0
  · rw [mul_eq_zero] at h
    wlog hf : f = 0 generalizing f g
    · simpa only [mul_comm, add_comm, and_comm,
        isCoprime_comm] using this g f h.symm (h.resolve_left hf)
    rw [hf, zero_mul, natSepDegree_zero, zero_add, isCoprime_zero_left, isUnit_iff, eq_comm,
      natSepDegree_eq_zero_iff, natDegree_eq_zero]
    refine ⟨fun ⟨x, h⟩ ↦ ?_, ?_⟩
    · by_cases hx : x = 0
      · exact .inl ⟨rfl, by rw [← h, hx, map_zero]⟩
      exact .inr ⟨x, Ne.isUnit hx, h⟩
    rintro (⟨-, h⟩ | ⟨x, -, h⟩)
    · exact ⟨0, by rw [h, map_zero]⟩
    exact ⟨x, h⟩
  classical
  simp_rw [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_mul h, Multiset.toFinset_add,
    Finset.card_union_eq_card_add_card, Finset.disjoint_iff_ne, Multiset.mem_toFinset, mem_aroots]
  rw [mul_eq_zero, not_or] at h
  refine ⟨fun H ↦ .inr (isCoprime_of_irreducible_dvd (not_and.2 fun _ ↦ h.2)
    fun u hu ⟨v, hf⟩ ⟨w, hg⟩ ↦ ?_), ?_⟩
  · obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero
      (AlgebraicClosure F) _ (degree_pos_of_irreducible hu).ne'
    exact H x ⟨h.1, by simpa only [map_mul, hx, zero_mul] using congr(aeval x $hf)⟩
      x ⟨h.2, by simpa only [map_mul, hx, zero_mul] using congr(aeval x $hg)⟩ rfl
  rintro (⟨rfl, rfl⟩ | hc)
  · exact (h.1 rfl).elim
  rintro x hf _ hg rfl
  obtain ⟨u, v, hfg⟩ := hc
  simpa only [map_add, map_mul, map_one, hf.2, hg.2, mul_zero, add_zero,
    zero_ne_one] using congr(aeval x $hfg)
/-
**Polynomial.natSepDegree_mul_of_isCoprime** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：natSepDegree_mul_of_isCoprime (g : F[X]) (hc : IsCoprime f g) : (f * g).na
tSepDegree = f.natSepDegree + g.natSepDegree
参数：g : F[X]；hc : IsCoprime f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natSepDegree_mul_eq_iff`：natSepDegree_mul_eq_iff (g : F[X]) :
 (f * g).natSepDegree = f.natSepDegree + g.natSepDegree ↔ (f = 0 ∧ g = 0) ∨ IsCo
prime f g
-/
theorem natSepDegree_mul_of_isCoprime (g : F[X]) (hc : IsCoprime f g) :
    (f * g).natSepDegree = f.natSepDegree + g.natSepDegree :=
  (natSepDegree_mul_eq_iff f g).2 (.inr hc)
/-
**Polynomial.natSepDegree_le_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_le_of_dvd (g : F[X]) (h1 : f ∣ g) (h2 : g != 0) : f.natSepDeg
ree <= g.natSepDegree
参数：g : F[X]；h1 : f ∣ g；h2 : g != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natSepDegree_eq_of_isAlgClosed`：natSepDegree_eq_of_isAlgClose
d [DecidableEq E] [IsAlgClosed E] : f.natSepDegree = (f.aroots E).toFinset.card
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.toFinset_subset`：toFinset_subset : s.toFinset subseteq t.toFins
et ↔ s subseteq t
· 使用定理 `Multiset.Le.subset`：∀ {α : Type u_1} {s t : Multiset α}, s ≤ t → s ⊆ t
· 使用定理 `Polynomial.roots.le_of_dvd`：∀ {R : Type u} [inst : CommRing R] [inst_1 :
 IsDomain R] {p q : Polynomial R}, q ≠ 0 → p ∣ q → p.roots ≤ q.roots
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.map_dvd`：map_dvd (f : R ->+* S) {x y : R[X]} : x ∣ y -> x.map
 f ∣ y.map f
-/
theorem natSepDegree_le_of_dvd (g : F[X]) (h1 : f ∣ g) (h2 : g ≠ 0) :
    f.natSepDegree ≤ g.natSepDegree := by
  classical
  simp_rw [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F)]
  exact Finset.card_le_card <| Multiset.toFinset_subset.mpr <|
    Multiset.Le.subset <| roots.le_of_dvd (map_ne_zero h2) <| map_dvd _ h1

/-- If a field `F` is of exponential characteristic `q`, then `Polynomial.expand F (q ^ n) f`
and `f` have the same separable degree. -/
/-
**Polynomial.natSepDegree_expand** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natSepDegree_expand (q : Nat) [hF : ExpChar F q] {n : Nat} : (expand F (q 
^ n) f).natSepDegree = f.natSepDegree
参数：q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Polynomial.expand_one`：expand_one (f : R[X]) : expand R 1 f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.natSepDegree_eq_of_isAlgClosed`：natSepDegree_eq_of_isAlgClose
d [DecidableEq E] [IsAlgClosed E] : f.natSepDegree = (f.aroots E).toFinset.card
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.map_expand`：map_expand {p : Nat} {f : R ->+* S} {q : R[X]} : 
map f (expand R p q) = expand S p (map f q)
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_eq`：card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card 
α = card β ↔ Nonempty (α ≃ β)
· 使用定理 `AlgebraicClosure.instCharP`：∀ (k : Type u) [inst : Field k] {p : ℕ} [Cha
rP k p], CharP (AlgebraicClosure k) p
· 使用定理 `IsAlgClosed.perfectField`：∀ (k : Type u) [inst : Field k] [IsAlgClosed k
], PerfectField k

--- 原说明 ---
If a field `F` is of exponential characteristic `q`, then `Polynomial.expand F (
q ^ n) f`
and `f` have the same separable degree.
-/
theorem natSepDegree_expand (q : ℕ) [hF : ExpChar F q] {n : ℕ} :
    (expand F (q ^ n) f).natSepDegree = f.natSepDegree := by
  obtain - | hprime := hF
  · simp only [one_pow, expand_one]
  have := Fact.mk hprime
  classical
  simpa only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_def, map_expand,
    Fintype.card_coe] using Fintype.card_eq.2
      ⟨(f.map (algebraMap F (AlgebraicClosure F))).rootsExpandPowEquivRoots q n⟩
/-
**Polynomial.natSepDegree_X_pow_char_pow_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：natSepDegree_X_pow_char_pow_sub_C (q : Nat) [ExpChar F q] (n : Nat) (y : F
) : (X ^ q ^ n - C y).natSepDegree = 1
参数：q : Nat；n : Nat；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.expand_X`：expand_X : expand R p X = X ^ p
· 使用定理 `Polynomial.expand_C`：expand_C (r : R) : expand R p (C r) = C r
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
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
· 使用定理 `Polynomial.natSepDegree_expand`：natSepDegree_expand (q : Nat) [hF : ExpC
har F q] {n : Nat} : (expand F (q ^ n) f).natSepDegree = f.natSepDegree
· 使用定理 `Polynomial.natSepDegree_X_sub_C`：natSepDegree_X_sub_C (x : F) : (X - C x
).natSepDegree = 1
-/
theorem natSepDegree_X_pow_char_pow_sub_C (q : ℕ) [ExpChar F q] (n : ℕ) (y : F) :
    (X ^ q ^ n - C y).natSepDegree = 1 := by
  rw [← expand_X, ← expand_C (q ^ n), ← map_sub, natSepDegree_expand, natSepDegree_X_sub_C]

variable {f} in
/-- If `g` is a separable contraction of `f`, then the separable degree of `f` is equal to
the degree of `g`. -/
/-
**Polynomial.IsSeparableContraction.natSepDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial.IsSeparableContraction`。
形式化陈述：∀ {F : Type u} [inst : Field F] {f g : Polynomial F} {q : ℕ} [ExpChar F q]
,   Polynomial.IsSeparableContraction q f g → f.natSepDegree = g.natDegree
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natSepDegree_expand`：natSepDegree_expand (q : Nat) [hF : ExpC
har F q] {n : Nat} : (expand F (q ^ n) f).natSepDegree = f.natSepDegree
· 使用定理 `Polynomial.Separable.natSepDegree_eq_natDegree`：∀ {F : Type u} [inst : F
ield F] {f : Polynomial F}, f.Separable → f.natSepDegree = f.natDegree

--- 原说明 ---
If `g` is a separable contraction of `f`, then the separable degree of `f` is eq
ual to
the degree of `g`.
-/
theorem IsSeparableContraction.natSepDegree_eq {g : Polynomial F} {q : ℕ} [ExpChar F q]
    (h : IsSeparableContraction q f g) : f.natSepDegree = g.natDegree := by
  obtain ⟨h1, m, h2⟩ := h
  rw [← h2, natSepDegree_expand, h1.natSepDegree_eq_natDegree]

variable {f} in
/-- If a polynomial has separable contraction, then its separable degree is equal to the degree of
the given separable contraction. -/
/-
**Polynomial.HasSeparableContraction.natSepDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial.HasSeparableContraction`。
形式化陈述：∀ {F : Type u} [inst : Field F] {f : Polynomial F} {q : ℕ} [ExpChar F q] (
hf : Polynomial.HasSeparableContraction q f),   f.natSepDegree = hf.degree
参数：hf : Polynomial.HasSeparableContraction q f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsSeparableContraction.natSepDegree_eq`：∀ {F : Type u} [inst 
: Field F] {f g : Polynomial F} {q : ℕ} [ExpChar F q],   Polynomial.IsSeparableC
ontraction q f g → f.natSepDegree = g.n…
· 使用定理 `Polynomial.HasSeparableContraction.isSeparableContraction`：∀ {F : Type u
_1} [inst : CommSemiring F] {q : ℕ} {f : Polynomial F} (hf : Polynomial.HasSepar
ableContraction q f),   Polynomial.IsSeparableC…

--- 原说明 ---
If a polynomial has separable contraction, then its separable degree is equal to
 the degree of
the given separable contraction.
-/
theorem HasSeparableContraction.natSepDegree_eq
    {q : ℕ} [ExpChar F q] (hf : f.HasSeparableContraction q) :
    f.natSepDegree = hf.degree := hf.isSeparableContraction.natSepDegree_eq

end Polynomial

namespace Irreducible

variable {F}
variable {f : F[X]}

/-- The separable degree of an irreducible polynomial divides its degree. -/
/-
**Irreducible.natSepDegree_dvd_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Irreducible`
。
形式化陈述：natSepDegree_dvd_natDegree (h : Irreducible f) : f.natSepDegree ∣ f.natDeg
ree
参数：h : Irreducible f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpChar.exists`：ExpChar.exists [Ring R] [IsDomain R] : exists q, ExpChar
 R q
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Irreducible.hasSeparableContraction`：∀ {F : Type u_1} [inst : Field F] (
q : ℕ) [hF : ExpChar F q] {f : Polynomial F},   Irreducible f → Polynomial.HasSe
parableContraction q f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.HasSeparableContraction.natSepDegree_eq`：∀ {F : Type u} [inst
 : Field F] {f : Polynomial F} {q : ℕ} [ExpChar F q] (hf : Polynomial.HasSeparab
leContraction q f),   f.natSepDegree = h…
· 使用定理 `Polynomial.HasSeparableContraction.dvd_degree`：∀ {F : Type u_1} [inst : 
CommSemiring F] {q : ℕ} {f : Polynomial F} (hf : Polynomial.HasSeparableContract
ion q f),   hf.degree ∣ f.natDegree

--- 原说明 ---
The separable degree of an irreducible polynomial divides its degree.
-/
theorem natSepDegree_dvd_natDegree (h : Irreducible f) :
    f.natSepDegree ∣ f.natDegree := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have hf := h.hasSeparableContraction q
  rw [hf.natSepDegree_eq]
  exact hf.dvd_degree

/-- A monic irreducible polynomial over a field `F` of exponential characteristic `q` has
separable degree one if and only if it is of the form `Polynomial.expand F (q ^ n) (X - C y)`
for some `n : ℕ` and `y : F`. -/
/-
**Irreducible.natSepDegree_eq_one_iff_of_monic'** 是 Mathlib 中的一个定理，位于命名空间 `Irred
ucible`。
形式化陈述：natSepDegree_eq_one_iff_of_monic' (q : Nat) [ExpChar F q] (hm : f.Monic) (
hi : Irreducible f) : f.natSepDegree = 1 ↔ exists (n : Nat) (y : F), f = expand 
F (q ^ n) (X - C y)
参数：q : Nat；hm : f.Monic；hi : Irreducible f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.hasSeparableContraction`：∀ {F : Type u_1} [inst : Field F] (
q : ℕ) [hF : ExpChar F q] {f : Polynomial F},   Irreducible f → Polynomial.HasSe
parableContraction q f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Separable.natSepDegree_eq_natDegree`：∀ {F : Type u} [inst : F
ield F] {f : Polynomial F}, f.Separable → f.natSepDegree = f.natDegree
· 使用定理 `Polynomial.natSepDegree_expand`：natSepDegree_expand (q : Nat) [hF : ExpC
har F q] {n : Nat} : (expand F (q ^ n) f).natSepDegree = f.natSepDegree
· 使用定理 `Polynomial.Monic.eq_X_add_C`：∀ {R : Type u} [inst : Semiring R] {p : Pol
ynomial R},   p.Monic → p.natDegree = 1 → p = Polynomial.X + Polynomial.C (p.coe
ff 0)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.monic_expand_iff`：monic_expand_iff {p : Nat} {f : R[X]} (hp :
 0 < p) : (expand R p f).Monic ↔ f.Monic
· 使用引理 `expChar_pow_pos`：expChar_pow_pos (q : Nat) [ExpChar R q] (n : Nat) : 0 <
 q ^ n
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Polynomial.natSepDegree_X_sub_C`：natSepDegree_X_sub_C (x : F) : (X - C x
).natSepDegree = 1

--- 原说明 ---
A monic irreducible polynomial over a field `F` of exponential characteristic `q
` has
separable degree one if and only if it is of the form `Polynomial.expand F (q ^ 
n) (X - C y)`
for some `n : ℕ` and `y : F`.
-/
theorem natSepDegree_eq_one_iff_of_monic' (q : ℕ) [ExpChar F q] (hm : f.Monic)
    (hi : Irreducible f) : f.natSepDegree = 1 ↔
    ∃ (n : ℕ) (y : F), f = expand F (q ^ n) (X - C y) := by
  refine ⟨fun h ↦ ?_, fun ⟨n, y, h⟩ ↦ ?_⟩
  · obtain ⟨g, h1, n, rfl⟩ := hi.hasSeparableContraction q
    have h2 : g.natDegree = 1 := by
      rwa [natSepDegree_expand _ q, h1.natSepDegree_eq_natDegree] at h
    rw [((monic_expand_iff <| expChar_pow_pos F q n).mp hm).eq_X_add_C h2]
    exact ⟨n, -(g.coeff 0), by rw [map_neg, sub_neg_eq_add]⟩
  rw [h, natSepDegree_expand _ q, natSepDegree_X_sub_C]

/-- A monic irreducible polynomial over a field `F` of exponential characteristic `q` has
separable degree one if and only if it is of the form `X ^ (q ^ n) - C y`
for some `n : ℕ` and `y : F`. -/
/-
**Irreducible.natSepDegree_eq_one_iff_of_monic** 是 Mathlib 中的一个定理，位于命名空间 `Irredu
cible`。
形式化陈述：natSepDegree_eq_one_iff_of_monic (q : Nat) [ExpChar F q] (hm : f.Monic) (h
i : Irreducible f) : f.natSepDegree = 1 ↔ exists (n : Nat) (y : F), f = X ^ q ^ 
n - C y
参数：q : Nat；hm : f.Monic；hi : Irreducible f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Irreducible.natSepDegree_eq_one_iff_of_monic'`：natSepDegree_eq_one_iff_o
f_monic' (q : Nat) [ExpChar F q] (hm : f.Monic) (hi : Irreducible f) : f.natSepD
egree = 1 ↔ exists (n : Nat) (y : F…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
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
· 使用定理 `Polynomial.expand_X`：expand_X : expand R p X = X ^ p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.expand_C`：expand_C (r : R) : expand R p (C r) = C r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A monic irreducible polynomial over a field `F` of exponential characteristic `q
` has
separable degree one if and only if it is of the form `X ^ (q ^ n) - C y`
for some `n : ℕ` and `y : F`.
-/
theorem natSepDegree_eq_one_iff_of_monic (q : ℕ) [ExpChar F q] (hm : f.Monic)
    (hi : Irreducible f) : f.natSepDegree = 1 ↔ ∃ (n : ℕ) (y : F), f = X ^ q ^ n - C y := by
  simp_rw [hi.natSepDegree_eq_one_iff_of_monic' q hm, map_sub, expand_X, expand_C]

end Irreducible

namespace Polynomial

namespace Monic

variable {F}
variable {f : F[X]}

alias natSepDegree_eq_one_iff_of_irreducible' := Irreducible.natSepDegree_eq_one_iff_of_monic'

alias natSepDegree_eq_one_iff_of_irreducible := Irreducible.natSepDegree_eq_one_iff_of_monic

/-- If a monic polynomial of separable degree one splits, then it is of form `(X - C y) ^ m` for
some non-zero natural number `m` and some element `y` of `F`. -/
/-
**Polynomial.Monic.eq_X_sub_C_pow_of_natSepDegree_eq_one_of_splits** 是 Mathlib 中
的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：eq_X_sub_C_pow_of_natSepDegree_eq_one_of_splits (hm : f.Monic) (hs : f.Spl
its) (h : f.natSepDegree = 1) : exists (m : Nat) (y : F), m != 0 ∧ f = (X - C y)
 ^ m
参数：hm : f.Monic；hs : f.Splits；h : f.natSepDegree = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.Splits.eq_prod_roots_of_monic`：∀ {R : Type u_1} [inst : CommR
ing R] {f : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f.Monic → f = (Mul
tiset.map (fun x => Polynomial…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natSepDegree_eq_of_splits`：natSepDegree_eq_of_splits [Decidab
leEq E] (h : (f.map (algebraMap F E)).Splits) : f.natSepDegree = (f.aroots E).to
Finset.card
· 使用定理 `Polynomial.Splits.map`：∀ {R : Type u_1} [inst : Semiring R] {f : Polynom
ial R},   f.Splits → ∀ {S : Type u_2} [inst_1 : Semiring S] (i : R →+* S), (Poly
nomial.map …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.toFinset_card_eq_one_iff`：toFinset_card_eq_one_iff (s : Multise
t α) : #s.toFinset = 1 ↔ Multiset.card s != 0 ∧ exists a : α, s = Multiset.card 
s • {a}
· 使用定理 `Polynomial.map_id`：map_id : p.map (RingHom.id _) = p
· 使用定理 `Algebra.algebraMap_self`：∀ {R : Type u} [inst : CommSemiring R], algebra
Map R R = RingHom.id R
· 使用定理 `Polynomial.aroots_def`：aroots_def (p : T[X]) (S) [CommRing S] [IsDomain 
S] [Algebra T S] : p.aroots S = (p.map (algebraMap T S)).roots
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `Multiset.prod_nsmul`：∀ {M : Type u_5} [inst : CommMonoid M] (m : Multise
t M) (n : ℕ), (n • m).prod = m.prod ^ n
· 使用定理 `Multiset.map_singleton`：map_singleton (f : α -> β) (a : α) : ({a} : Mult
iset α).map f = {f a}
· 使用引理 `Multiset.map_nsmul`：map_nsmul (f : α -> β) (n : Nat) (s) : map f (n • s)
 = n • map f s

--- 原说明 ---
If a monic polynomial of separable degree one splits, then it is of form `(X - C
 y) ^ m` for
some non-zero natural number `m` and some element `y` of `F`.
-/
theorem eq_X_sub_C_pow_of_natSepDegree_eq_one_of_splits (hm : f.Monic)
    (hs : f.Splits)
    (h : f.natSepDegree = 1) : ∃ (m : ℕ) (y : F), m ≠ 0 ∧ f = (X - C y) ^ m := by
  classical
  have h1 := hs.eq_prod_roots_of_monic hm
  have h2 := (natSepDegree_eq_of_splits f (hs.map <| .id F)).symm
  rw [h, aroots_def, Algebra.algebraMap_self, map_id, Multiset.toFinset_card_eq_one_iff] at h2
  obtain ⟨h2, y, h3⟩ := h2
  exact ⟨_, y, h2, by rwa [h3, Multiset.map_nsmul, Multiset.map_singleton, Multiset.prod_nsmul,
    Multiset.prod_singleton] at h1⟩

/-- If a monic irreducible polynomial over a field `F` of exponential characteristic `q` has
separable degree one, then it is of the form `X ^ (q ^ n) - C y` for some natural number `n`,
and some element `y` of `F`, such that either `n = 0` or `y` has no `q`-th root in `F`. -/
/-
**Polynomial.Monic.eq_X_pow_char_pow_sub_C_of_natSepDegree_eq_one_of_irreducible
** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：eq_X_pow_char_pow_sub_C_of_natSepDegree_eq_one_of_irreducible (q : Nat) [E
xpChar F q] (hm : f.Monic) (hi : Irreducible f) (h : f.natSepDegree = 1) : exist
s (n : Nat) (y : F), (n = 0 ∨ y ∉ (frobenius F q).range) ∧ f = X ^ q ^ n - C y
参数：q : Nat；hm : f.Monic；hi : Irreducible f；h : f.natSepDegree = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.Monic.natSepDegree_eq_one_iff_of_irreducible`：∀ {F : Type u} 
[inst : Field F] {f : Polynomial F} (q : ℕ) [ExpChar F q],   f.Monic → Irreducib
le f → (f.natSepDegree = 1 ↔ ∃ n y, f = Polyn…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用引理 `expChar_of_injective_ringHom`：expChar_of_injective_ringHom [NonAssocSemi
ring R] [NonAssocSemiring A] {f : R ->+* A} (h : Function.Injective f) (q : Nat)
 [hR : ExpChar R q…
· 使用定理 `Polynomial.C_injective`：C_injective : Injective (C : R -> R[X])
· 使用引理 `not_irreducible_pow`：not_irreducible_pow : forall {n : Nat}, n != 1 -> ¬
 Irreducible (x ^ n) | 0, _ => by simp | n + 2, _ => by intro ⟨h₁, h₂⟩ have
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用引理 `sub_pow_expChar`：sub_pow_expChar : (x - y) ^ p = x ^ p - y ^ p
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `frobenius_def`：frobenius_def : frobenius R p x = x ^ p
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Nat.succ_pred`：∀ {a : ℕ}, a ≠ 0 → a.pred.succ = a
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p

--- 原说明 ---
If a monic irreducible polynomial over a field `F` of exponential characteristic
 `q` has
separable degree one, then it is of the form `X ^ (q ^ n) - C y` for some natura
l number `n`,
and some element `y` of `F`, such that either `n = 0` or `y` has no `q`-th root 
in `F`.
-/
theorem eq_X_pow_char_pow_sub_C_of_natSepDegree_eq_one_of_irreducible (q : ℕ) [ExpChar F q]
    (hm : f.Monic) (hi : Irreducible f) (h : f.natSepDegree = 1) : ∃ (n : ℕ) (y : F),
      (n = 0 ∨ y ∉ (frobenius F q).range) ∧ f = X ^ q ^ n - C y := by
  obtain ⟨n, y, hf⟩ := (hm.natSepDegree_eq_one_iff_of_irreducible q hi).1 h
  cases id ‹ExpChar F q› with
  | zero =>
    simp_rw [one_pow, pow_one] at hf ⊢
    exact ⟨0, y, .inl rfl, hf⟩
  | prime hq =>
    refine ⟨n, y, (em _).imp id fun hn ⟨z, hy⟩ ↦ ?_, hf⟩
    have := expChar_of_injective_ringHom (R := F) C_injective q
    rw [hf, ← Nat.succ_pred hn, pow_succ, pow_mul, ← hy, frobenius_def, map_pow,
      ← sub_pow_expChar] at hi
    exact not_irreducible_pow hq.ne_one hi

/-- If a monic polynomial over a field `F` of exponential characteristic `q` has separable degree
one, then it is of the form `(X ^ (q ^ n) - C y) ^ m` for some non-zero natural number `m`,
some natural number `n`, and some element `y` of `F`, such that either `n = 0` or `y` has no
`q`-th root in `F`. -/
/-
**Polynomial.Monic.eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one** 是 Mathli
b 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one (q : Nat) [ExpChar F q]
 (hm : f.Monic) (h : f.natSepDegree = 1) : exists (m n : Nat) (y : F), m != 0 ∧ 
(n = 0 ∨ y ∉ (frobenius F q).range) ∧ f = (X ^ q ^ n - C y) ^ m
参数：q : Nat；hm : f.Monic；h : f.natSepDegree = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.exists_monic_irreducible_factor`：Polynomial.exists_monic_irre
ducible_factor {F : Type*} [Field F] (f : F[X]) (hu : ¬IsUnit f) : exists g : F[
X], g.Monic ∧ Irreducible g ∧ g …
· 使用引理 `Polynomial.not_isUnit_of_natDegree_pos`：not_isUnit_of_natDegree_pos (p :
 R[X]) (hpl : 0 < p.natDegree) : ¬ IsUnit p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.natSepDegree_ne_zero_iff`：natSepDegree_ne_zero_iff : f.natSep
Degree != 0 ↔ f.natDegree != 0
· 使用定理 `Nat.one_ne_zero`：1 ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Polynomial.natSepDegree_le_of_dvd`：natSepDegree_le_of_dvd (g : F[X]) (h1
 : f ∣ g) (h2 : g != 0) : f.natSepDegree <= g.natSepDegree
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Irreducible.natDegree_pos`：natDegree_pos (h : Irreducible f) : 0 < f.nat
Degree
· 使用定理 `Polynomial.Monic.eq_X_pow_char_pow_sub_C_of_natSepDegree_eq_one_of_irred
ucible`：eq_X_pow_char_pow_sub_C_of_natSepDegree_eq_one_of_irreducible (q : Nat) 
[ExpChar F q] (hm : f.Monic) (hi : Irreducible f) (h : f.natSepDegre…
· 使用定理 `Polynomial.finiteMultiplicity_of_degree_pos_of_monic`：finiteMultiplicity
_of_degree_pos_of_monic (hp : (0 : WithBot Nat) < degree p) (hmp : Monic p) (hq 
: q != 0) : FiniteMultiplicity p q
· 使用定理 `Polynomial.degree_pos_of_irreducible`：degree_pos_of_irreducible (hp : Ir
reducible p) : 0 < p.degree
· 使用定理 `multiplicity_pos_of_dvd`：multiplicity_pos_of_dvd (hdiv : a ∣ b) : 0 < mu
ltiplicity a b
· 使用定理 `FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd`：FiniteMultiplicity.exi
sts_eq_pow_mul_and_not_dvd (hfin : FiniteMultiplicity a b) : exists c : α, b = a
 ^ multiplicity a b * c ∧ ¬a ∣ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.eq_one_of_monic_natDegree_zero`：eq_one_of_monic_natDegree_zer
o (hf : p.Monic) (hfd : p.natDegree = 0) : p = 1
· 使用定理 `Polynomial.Monic.of_mul_monic_left`：∀ {R : Type u} [inst : Semiring R] {
p q : Polynomial R}, p.Monic → (p * q).Monic → q.Monic
· 使用定理 `Polynomial.Monic.pow`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic → ∀ (n : ℕ), (p ^ n).Monic
· 使用定理 `Polynomial.natSepDegree_eq_zero_iff`：natSepDegree_eq_zero_iff : f.natSep
Degree = 0 ↔ f.natDegree = 0
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
If a monic polynomial over a field `F` of exponential characteristic `q` has sep
arable degree
one, then it is of the form `(X ^ (q ^ n) - C y) ^ m` for some non-zero natural 
number `m`,
some natural number `n`, and some element `y` of `F`, such that either `n = 0` o
r `y` has no
`q`-th root in `F`.
-/
theorem eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one (q : ℕ) [ExpChar F q] (hm : f.Monic)
    (h : f.natSepDegree = 1) : ∃ (m n : ℕ) (y : F),
      m ≠ 0 ∧ (n = 0 ∨ y ∉ (frobenius F q).range) ∧ f = (X ^ q ^ n - C y) ^ m := by
  obtain ⟨p, hM, hI, hf⟩ := exists_monic_irreducible_factor _ <| not_isUnit_of_natDegree_pos _
    <| Nat.pos_of_ne_zero <| (natSepDegree_ne_zero_iff _).1 (h.symm ▸ Nat.one_ne_zero)
  have hD := (h ▸ natSepDegree_le_of_dvd p f hf hm.ne_zero).antisymm <|
    Nat.pos_of_ne_zero <| (natSepDegree_ne_zero_iff _).2 hI.natDegree_pos.ne'
  obtain ⟨n, y, H, hp⟩ := hM.eq_X_pow_char_pow_sub_C_of_natSepDegree_eq_one_of_irreducible q hI hD
  have hF := finiteMultiplicity_of_degree_pos_of_monic (degree_pos_of_irreducible hI) hM hm.ne_zero
  have hne := (multiplicity_pos_of_dvd hf).ne'
  refine ⟨_, n, y, hne, H, ?_⟩
  obtain ⟨c, hf, H⟩ := hF.exists_eq_pow_mul_and_not_dvd
  rw [hf, natSepDegree_mul_of_isCoprime _ c <| IsCoprime.pow_left <|
    (hI.isCoprime_or_dvd c).resolve_right H, natSepDegree_pow_of_ne_zero _ hne, hD,
    add_eq_left, natSepDegree_eq_zero_iff] at h
  simpa only [eq_one_of_monic_natDegree_zero ((hM.pow _).of_mul_monic_left (hf ▸ hm)) h,
    mul_one, ← hp] using hf

/-- A monic polynomial over a field `F` of exponential characteristic `q` has separable degree one
if and only if it is of the form `(X ^ (q ^ n) - C y) ^ m` for some non-zero natural number `m`,
some natural number `n`, and some element `y` of `F`. -/
/-
**Polynomial.Monic.natSepDegree_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
.Monic`。
形式化陈述：natSepDegree_eq_one_iff (q : Nat) [ExpChar F q] (hm : f.Monic) : f.natSepD
egree = 1 ↔ exists (m n : Nat) (y : F), m != 0 ∧ f = (X ^ q ^ n - C y) ^ m
参数：q : Nat；hm : f.Monic。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one`：eq_
X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one (q : Nat) [ExpChar F q] (hm : f.
Monic) (h : f.natSepDegree = 1) : exists (m n : Nat) (y :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natSepDegree_pow`：natSepDegree_pow {n : Nat} : (f ^ n).natSep
Degree = if n = 0 then 0 else f.natSepDegree
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.natSepDegree_X_pow_char_pow_sub_C`：natSepDegree_X_pow_char_po
w_sub_C (q : Nat) [ExpChar F q] (n : Nat) (y : F) : (X ^ q ^ n - C y).natSepDegr
ee = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A monic polynomial over a field `F` of exponential characteristic `q` has separa
ble degree one
if and only if it is of the form `(X ^ (q ^ n) - C y) ^ m` for some non-zero nat
ural number `m`,
some natural number `n`, and some element `y` of `F`.
-/
theorem natSepDegree_eq_one_iff (q : ℕ) [ExpChar F q] (hm : f.Monic) :
    f.natSepDegree = 1 ↔ ∃ (m n : ℕ) (y : F), m ≠ 0 ∧ f = (X ^ q ^ n - C y) ^ m := by
  refine ⟨fun h ↦ ?_, fun ⟨m, n, y, hm, h⟩ ↦ ?_⟩
  · obtain ⟨m, n, y, hm, -, h⟩ := hm.eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one q h
    exact ⟨m, n, y, hm, h⟩
  simp_rw [h, natSepDegree_pow, hm, ite_false, natSepDegree_X_pow_char_pow_sub_C]

end Monic

end Polynomial

namespace minpoly

variable {F : Type u} {E : Type v} [Field F] [Ring E] [IsDomain E] [Algebra F E]
variable (q : ℕ) [hF : ExpChar F q] {x : E}

/-- The minimal polynomial of an element of `E / F` of exponential characteristic `q` has
separable degree one if and only if the minimal polynomial is of the form
`Polynomial.expand F (q ^ n) (X - C y)` for some `n : ℕ` and `y : F`. -/
/-
**minpoly.natSepDegree_eq_one_iff_eq_expand_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `m
inpoly`。
形式化陈述：natSepDegree_eq_one_iff_eq_expand_X_sub_C : (minpoly F x).natSepDegree = 1
 ↔ exists (n : Nat) (y : F), minpoly F x = expand F (q ^ n) (X - C y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.eq_zero`：eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0
· 使用定理 `Polynomial.natSepDegree_zero`：natSepDegree_zero : (0 : F[X]).natSepDegre
e = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Irreducible.natSepDegree_eq_one_iff_of_monic'`：natSepDegree_eq_one_iff_o
f_monic' (q : Nat) [ExpChar F q] (hm : f.Monic) (hi : Irreducible f) : f.natSepD
egree = 1 ↔ exists (n : Nat) (y : F…
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `minpoly.irreducible`：irreducible (hx : IsIntegral A x) : Irreducible (mi
npoly A x)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.natSepDegree_expand`：natSepDegree_expand (q : Nat) [hF : ExpC
har F q] {n : Nat} : (expand F (q ^ n) f).natSepDegree = f.natSepDegree
· 使用定理 `Polynomial.natSepDegree_X_sub_C`：natSepDegree_X_sub_C (x : F) : (X - C x
).natSepDegree = 1

--- 原说明 ---
The minimal polynomial of an element of `E / F` of exponential characteristic `q
` has
separable degree one if and only if the minimal polynomial is of the form
`Polynomial.expand F (q ^ n) (X - C y)` for some `n : ℕ` and `y : F`.
-/
theorem natSepDegree_eq_one_iff_eq_expand_X_sub_C : (minpoly F x).natSepDegree = 1 ↔
    ∃ (n : ℕ) (y : F), minpoly F x = expand F (q ^ n) (X - C y) := by
  refine ⟨fun h ↦ ?_, fun ⟨n, y, h⟩ ↦ ?_⟩
  · have halg : IsIntegral F x := by_contra fun h' ↦ by
      simp only [eq_zero h', natSepDegree_zero, zero_ne_one] at h
    exact (minpoly.irreducible halg).natSepDegree_eq_one_iff_of_monic' q
      (minpoly.monic halg) |>.1 h
  rw [h, natSepDegree_expand _ q, natSepDegree_X_sub_C]

/-- The minimal polynomial of an element of `E / F` of exponential characteristic `q` has
separable degree one if and only if the minimal polynomial is of the form
`X ^ (q ^ n) - C y` for some `n : ℕ` and `y : F`. -/
/-
**minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `minp
oly`。
形式化陈述：natSepDegree_eq_one_iff_eq_X_pow_sub_C : (minpoly F x).natSepDegree = 1 ↔ 
exists (n : Nat) (y : F), minpoly F x = X ^ q ^ n - C y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.natSepDegree_eq_one_iff_eq_expand_X_sub_C`：natSepDegree_eq_one_i
ff_eq_expand_X_sub_C : (minpoly F x).natSepDegree = 1 ↔ exists (n : Nat) (y : F)
, minpoly F x = expand F (q ^ n) (X - C…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.expand_X`：expand_X : expand R p X = X ^ p
· 使用定理 `Polynomial.expand_C`：expand_C (r : R) : expand R p (C r) = C r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The minimal polynomial of an element of `E / F` of exponential characteristic `q
` has
separable degree one if and only if the minimal polynomial is of the form
`X ^ (q ^ n) - C y` for some `n : ℕ` and `y : F`.
-/
theorem natSepDegree_eq_one_iff_eq_X_pow_sub_C : (minpoly F x).natSepDegree = 1 ↔
    ∃ (n : ℕ) (y : F), minpoly F x = X ^ q ^ n - C y := by
  simp only [minpoly.natSepDegree_eq_one_iff_eq_expand_X_sub_C q, map_sub, expand_X, expand_C]

/-- The minimal polynomial of an element `x` of `E / F` of exponential characteristic `q` has
separable degree one if and only if `x ^ (q ^ n) ∈ F` for some `n : ℕ`. -/
/-
**minpoly.natSepDegree_eq_one_iff_pow_mem** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：natSepDegree_eq_one_iff_pow_mem : (minpoly F x).natSepDegree = 1 ↔ exists 
n : Nat, x ^ q ^ n in (algebraMap F E).range
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
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
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C`：natSepDegree_eq_one_iff_
eq_X_pow_sub_C : (minpoly F x).natSepDegree = 1 ↔ exists (n : Nat) (y : F), minp
oly F x = X ^ q ^ n - C y
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `Polynomial.X_pow_sub_C_ne_zero`：X_pow_sub_C_ne_zero {n : Nat} (hn : 0 < 
n) (a : R) : (X : R[X]) ^ n - C a != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `expChar_pow_pos`：expChar_pow_pos (q : Nat) [ExpChar R q] (n : Nat) : 0 <
 q ^ n
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Polynomial.natSepDegree_le_of_dvd`：natSepDegree_le_of_dvd (g : F[X]) (h1
 : f ∣ g) (h2 : g != 0) : f.natSepDegree <= g.natSepDegree
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `Polynomial.natSepDegree_X_pow_char_pow_sub_C`：natSepDegree_X_pow_char_po
w_sub_C (q : Nat) [ExpChar F q] (n : Nat) (y : F) : (X ^ q ^ n - C y).natSepDegr
ee = 1
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The minimal polynomial of an element `x` of `E / F` of exponential characteristi
c `q` has
separable degree one if and only if `x ^ (q ^ n) ∈ F` for some `n : ℕ`.
-/
theorem natSepDegree_eq_one_iff_pow_mem : (minpoly F x).natSepDegree = 1 ↔
    ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  convert_to _ ↔ ∃ (n : ℕ) (y : F), Polynomial.aeval x (X ^ q ^ n - C y) = 0
  · simp_rw [RingHom.mem_range, map_sub, map_pow, aeval_C, aeval_X, sub_eq_zero, eq_comm]
  refine ⟨fun h ↦ ?_, fun ⟨n, y, h⟩ ↦ ?_⟩
  · obtain ⟨n, y, hx⟩ := (minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q).1 h
    exact ⟨n, y, hx ▸ aeval F x⟩
  have hnezero := X_pow_sub_C_ne_zero (expChar_pow_pos F q n) y
  refine ((natSepDegree_le_of_dvd _ _ (minpoly.dvd F x h) hnezero).trans_eq <|
    natSepDegree_X_pow_char_pow_sub_C q n y).antisymm ?_
  rw [Nat.one_le_iff_ne_zero, natSepDegree_ne_zero_iff, ← Nat.one_le_iff_ne_zero]
  exact minpoly.natDegree_pos <| IsAlgebraic.isIntegral ⟨_, hnezero, h⟩

/-- The minimal polynomial of an element `x` of `E / F` of exponential characteristic `q` has
separable degree one if and only if the minimal polynomial is of the form
`(X - x) ^ (q ^ n)` for some `n : ℕ`. -/
/-
**minpoly.natSepDegree_eq_one_iff_eq_X_sub_C_pow** 是 Mathlib 中的一个定理，位于命名空间 `minp
oly`。
形式化陈述：natSepDegree_eq_one_iff_eq_X_sub_C_pow : (minpoly F x).natSepDegree = 1 ↔ 
exists n : Nat, (minpoly F x).map (algebraMap F E) = (X - C x) ^ q ^ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `expChar_of_injective_algebraMap`：expChar_of_injective_algebraMap [CommSe
miring R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A)) (
q : Nat) [ExpChar R q…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `expChar_of_injective_ringHom`：expChar_of_injective_ringHom [NonAssocSemi
ring R] [NonAssocSemiring A] {f : R ->+* A} (h : Function.Injective f) (q : Nat)
 [hR : ExpChar R q…
· 使用定理 `Polynomial.C_injective`：C_injective : Injective (C : R -> R[X])
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C`：natSepDegree_eq_one_iff_
eq_X_pow_sub_C : (minpoly F x).natSepDegree = 1 ↔ exists (n : Nat) (y : F), minp
oly F x = X ^ q ^ n - C y
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
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
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用引理 `sub_pow_expChar_pow_of_commute`：sub_pow_expChar_pow_of_commute (h : Comm
ute x y) : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n
· 使用定理 `Polynomial.commute_X`：commute_X (p : R[X]) : Commute X p
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
The minimal polynomial of an element `x` of `E / F` of exponential characteristi
c `q` has
separable degree one if and only if the minimal polynomial is of the form
`(X - x) ^ (q ^ n)` for some `n : ℕ`.
-/
theorem natSepDegree_eq_one_iff_eq_X_sub_C_pow : (minpoly F x).natSepDegree = 1 ↔
    ∃ n : ℕ, (minpoly F x).map (algebraMap F E) = (X - C x) ^ q ^ n := by
  have := expChar_of_injective_algebraMap (algebraMap F E).injective q
  have := expChar_of_injective_ringHom (C_injective (R := E)) q
  refine ⟨fun h ↦ ?_, fun ⟨n, h⟩ ↦ (natSepDegree_eq_one_iff_pow_mem q).2 ?_⟩
  · obtain ⟨n, y, h⟩ := (natSepDegree_eq_one_iff_eq_X_pow_sub_C q).1 h
    have hx := congr_arg (Polynomial.aeval x) h.symm
    rw [minpoly.aeval, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero, eq_comm] at hx
    use n
    rw [h, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, hx, map_pow,
      ← sub_pow_expChar_pow_of_commute _ _ (commute_X _)]
  apply_fun constantCoeff at h
  simp_rw [map_pow, map_sub, constantCoeff_apply, coeff_map, coeff_X_zero, coeff_C_zero] at h
  rw [zero_sub, neg_pow, neg_one_pow_expChar_pow] at h
  exact ⟨n, -(minpoly F x).coeff 0, by rw [map_neg, h, neg_mul, one_mul, neg_neg]⟩

end minpoly

namespace IntermediateField

/-- The separable degree of `F⟮α⟯ / F` is equal to the separable degree of the
minimal polynomial of `α` over `F`. -/
/-
**IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree** 是 Mathlib 中的一个定
理，位于命名空间 `IntermediateField`。
形式化陈述：finSepDegree_adjoin_simple_eq_natSepDegree {α : E} (halg : IsAlgebraic F α
) : finSepDegree F F⟮α⟯ = (minpoly F α).natSepDegree
参数：halg : IsAlgebraic F α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Polynomial.natSepDegree_eq_of_isAlgClosed`：natSepDegree_eq_of_isAlgClose
d [DecidableEq E] [IsAlgClosed E] : f.natSepDegree = (f.aroots E).toFinset.card
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The separable degree of `F⟮α⟯ / F` is equal to the separable degree of the
minimal polynomial of `α` over `F`.
-/
theorem finSepDegree_adjoin_simple_eq_natSepDegree {α : E} (halg : IsAlgebraic F α) :
    finSepDegree F F⟮α⟯ = (minpoly F α).natSepDegree := by
  have : finSepDegree F F⟮α⟯ = _ := Nat.card_congr
    (algHomAdjoinIntegralEquiv F (K := AlgebraicClosure F⟮α⟯) halg.isIntegral)
  classical
  rw [this, Nat.card_eq_fintype_card, natSepDegree_eq_of_isAlgClosed (E := AlgebraicClosure F⟮α⟯),
    ← Fintype.card_coe]
  simp_rw [Multiset.mem_toFinset]

-- The separable degree of `F⟮α⟯ / F` divides the degree of `F⟮α⟯ / F`.
-- Marked as `private` because it is a special case of `finSepDegree_dvd_finrank`.
/-
**IntermediateField.finSepDegree_adjoin_simple_dvd_finrank** 是 Mathlib 中的一个定理，位于
命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem finSepDegree_adjoin_simple_dvd_finrank (α : E) :
    finSepDegree F F⟮α⟯ ∣ finrank F F⟮α⟯ := by
  by_cases halg : IsAlgebraic F α
  · rw [finSepDegree_adjoin_simple_eq_natSepDegree F E halg, adjoin.finrank halg.isIntegral]
    exact (minpoly.irreducible halg.isIntegral).natSepDegree_dvd_natDegree
  have : finrank F F⟮α⟯ = 0 := finrank_of_infinite_dimensional fun _ ↦
    halg ((AdjoinSimple.isIntegral_gen F α).1 (IsIntegral.of_finite F _)).isAlgebraic
  rw [this]
  exact dvd_zero _

/-- The separable degree of `F⟮α⟯ / F` is smaller than the degree of `F⟮α⟯ / F` if `α` is
algebraic over `F`. -/
/-
**IntermediateField.finSepDegree_adjoin_simple_le_finrank** 是 Mathlib 中的一个定理，位于命
名空间 `IntermediateField`。
形式化陈述：finSepDegree_adjoin_simple_le_finrank (α : E) (halg : IsAlgebraic F α) : f
inSepDegree F F⟮α⟯ <= finrank F F⟮α⟯
参数：α : E；halg : IsAlgebraic F α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `_private.Mathlib.FieldTheory.SeparableDegree.0.IntermediateField.finSepD
egree_adjoin_simple_dvd_finrank`：∀ (F : Type u) (E : Type v) [inst : Field F] [i
nst_1 : Field E] [inst_2 : Algebra F E] (α : E),   Field.finSepDegree F ↥F⟮α⟯ ∣ 
Module.finran…

--- 原说明 ---
The separable degree of `F⟮α⟯ / F` is smaller than the degree of `F⟮α⟯ / F` if `
α` is
algebraic over `F`.
-/
theorem finSepDegree_adjoin_simple_le_finrank (α : E) (halg : IsAlgebraic F α) :
    finSepDegree F F⟮α⟯ ≤ finrank F F⟮α⟯ := by
  have := adjoin.finiteDimensional halg.isIntegral
  exact Nat.le_of_dvd finrank_pos <| finSepDegree_adjoin_simple_dvd_finrank F E α

/-- If `α` is algebraic over `F`, then the separable degree of `F⟮α⟯ / F` is equal to the degree
of `F⟮α⟯ / F` if and only if `α` is a separable element. -/
/-
**IntermediateField.finSepDegree_adjoin_simple_eq_finrank_iff** 是 Mathlib 中的一个定理
，位于命名空间 `IntermediateField`。
形式化陈述：finSepDegree_adjoin_simple_eq_finrank_iff (α : E) (halg : IsAlgebraic F α)
 : finSepDegree F F⟮α⟯ = finrank F F⟮α⟯ ↔ IsSeparable F α
参数：α : E；halg : IsAlgebraic F α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree`：finSepDegr
ee_adjoin_simple_eq_natSepDegree {α : E} (halg : IsAlgebraic F α) : finSepDegree
 F F⟮α⟯ = (minpoly F α).natSepDegree
· 使用定理 `IntermediateField.adjoin.finrank`：∀ {K : Type u} [inst : Field K] {L : T
ype u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegral K x → M
odule.finrank K ↥K⟮x⟯ …
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `Polynomial.natSepDegree_eq_natDegree_iff`：natSepDegree_eq_natDegree_iff 
(hf : f != 0) : f.natSepDegree = f.natDegree ↔ f.Separable
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsSeparable.eq_1`：∀ (F : Type u_1) {K : Type u_3} [inst : CommRing F] [i
nst_1 : Ring K] [inst_2 : Algebra F K] (x : K),   IsSeparable F x = (minpoly F x
).Sepa…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If `α` is algebraic over `F`, then the separable degree of `F⟮α⟯ / F` is equal t
o the degree
of `F⟮α⟯ / F` if and only if `α` is a separable element.
-/
theorem finSepDegree_adjoin_simple_eq_finrank_iff (α : E) (halg : IsAlgebraic F α) :
    finSepDegree F F⟮α⟯ = finrank F F⟮α⟯ ↔ IsSeparable F α := by
  rw [finSepDegree_adjoin_simple_eq_natSepDegree F E halg, adjoin.finrank halg.isIntegral,
    natSepDegree_eq_natDegree_iff _ (minpoly.ne_zero halg.isIntegral), IsSeparable]

end IntermediateField

namespace Field

/-- The separable degree of any field extension `E / F` divides the degree of `E / F`. -/
/-
**Field.finSepDegree_dvd_finrank** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：finSepDegree_dvd_finrank : finSepDegree F E ∣ finrank F E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.finSepDegree_top`：finSepDegree_top : finSepDegree F (⊤
 : IntermediateField E K) = finSepDegree F K
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
· 使用定理 `IntermediateField.induction_on_adjoin`：induction_on_adjoin [FiniteDimens
ional F E] (P : IntermediateField F E -> Prop) (base : P ⊥) (ih : forall (K : In
termediateField F E) (x : E…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IntermediateField.finSepDegree_bot`：finSepDegree_bot : finSepDegree F (⊥
 : IntermediateField F E) = 1
· 使用定理 `IntermediateField.finrank_bot`：∀ {F : Type u_1} [inst : Field F] {E : Ty
pe u_2} [inst_1 : Field E] [inst_2 : Algebra F E], Module.finrank F ↥⊥ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_dvd_mul`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a 
∣ b → c ∣ d → a * c ∣ b * d
· 使用定理 `_private.Mathlib.FieldTheory.SeparableDegree.0.IntermediateField.finSepD
egree_adjoin_simple_dvd_finrank`：∀ (F : Type u) (E : Type v) [inst : Field F] [i
nst_1 : Field E] [inst_2 : Algebra F E] (α : E),   Field.finSepDegree F ↥F⟮α⟯ ∣ 
Module.finran…
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
· 使用定理 `IntermediateField.instIsScalarTowerSubtypeMem_1`：∀ {K : Type u_1} {L : T
ype u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] {S : Interme
diateField K L}   {E : Type u_4} [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Field.finSepDegree_mul_finSepDegree_of_isAlgebraic`：finSepDegree_mul_fin
SepDegree_of_isAlgebraic [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebrai
c E K] : finSepDegree F E * finSepDegree…
· 使用定理 `Module.finrank_of_infinite_dimensional`：finrank_of_infinite_dimensional 
(h : ¬FiniteDimensional K V) : finrank K V = 0
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0

--- 原说明 ---
The separable degree of any field extension `E / F` divides the degree of `E / F
`.
-/
theorem finSepDegree_dvd_finrank : finSepDegree F E ∣ finrank F E := by
  by_cases hfd : FiniteDimensional F E
  · rw [← finSepDegree_top F, ← finrank_top F E]
    refine induction_on_adjoin (fun K : IntermediateField F E ↦ finSepDegree F K ∣ finrank F K)
      (by simp_rw [finSepDegree_bot, IntermediateField.finrank_bot, one_dvd]) (fun L x h ↦ ?_) ⊤
    have hdvd := mul_dvd_mul h <| finSepDegree_adjoin_simple_dvd_finrank L E x
    set M := L⟮x⟯
    rwa [finSepDegree_mul_finSepDegree_of_isAlgebraic F L M,
      Module.finrank_mul_finrank F L M] at hdvd
  rw [finrank_of_infinite_dimensional hfd]
  exact dvd_zero _

/-- The separable degree of a finite extension `E / F` is smaller than the degree of `E / F`. -/
@[stacks 09HA "The inequality"]
/-
**Field.finSepDegree_le_finrank** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：finSepDegree_le_finrank [FiniteDimensional F E] : finSepDegree F E <= finr
ank F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Field.finSepDegree_dvd_finrank`：finSepDegree_dvd_finrank : finSepDegree 
F E ∣ finrank F E

--- 原说明 ---
The separable degree of a finite extension `E / F` is smaller than the degree of
 `E / F`.
-/
theorem finSepDegree_le_finrank [FiniteDimensional F E] :
    finSepDegree F E ≤ finrank F E := Nat.le_of_dvd finrank_pos <| finSepDegree_dvd_finrank F E

/-- If `E / F` is a separable extension, then its separable degree is equal to its degree.
When `E / F` is infinite, it means that `Field.Emb F E` has infinitely many elements.
(But the cardinality of `Field.Emb F E` is not equal to `Module.rank F E` in general!) -/
/-
**Field.finSepDegree_eq_finrank_of_isSeparable** 是 Mathlib 中的一个定理，位于命名空间 `Field`
。
形式化陈述：finSepDegree_eq_finrank_of_isSeparable [Algebra.IsSeparable F E] : finSepD
egree F E = finrank F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.finSepDegree_top`：finSepDegree_top : finSepDegree F (⊤
 : IntermediateField E K) = finSepDegree F K
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
· 使用定理 `IntermediateField.induction_on_adjoin`：induction_on_adjoin [FiniteDimens
ional F E] (P : IntermediateField F E -> Prop) (base : P ⊥) (ih : forall (K : In
termediateField F E) (x : E…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IntermediateField.finSepDegree_bot`：finSepDegree_bot : finSepDegree F (⊥
 : IntermediateField F E) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IntermediateField.finrank_bot`：∀ {F : Type u_1} [inst : Field F] {E : Ty
pe u_2} [inst_1 : Field E] [inst_2 : Algebra F E], Module.finrank F ↥⊥ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.finSepDegree_adjoin_simple_eq_finrank_iff`：finSepDegre
e_adjoin_simple_eq_finrank_iff (α : E) (halg : IsAlgebraic F α) : finSepDegree F
 F⟮α⟯ = finrank F F⟮α⟯ ↔ IsSeparable F α
· 使用定理 `IsAlgebraic.of_finite`：IsAlgebraic.of_finite (e : A) [Module.Finite R A]
 : IsAlgebraic R e
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsSeparable.tower_top`：IsSeparable.tower_top {x : E} (h : IsSeparable F 
x) : IsSeparable L x
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
· 使用定理 `IntermediateField.instIsScalarTowerSubtypeMem_1`：∀ {K : Type u_1} {L : T
ype u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] {S : Interme
diateField K L}   {E : Type u_4} [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Field.finSepDegree_mul_finSepDegree_of_isAlgebraic`：finSepDegree_mul_fin
SepDegree_of_isAlgebraic [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebrai
c E K] : finSepDegree F E * finSepDegree…
· 使用定理 `Module.finrank_of_infinite_dimensional`：finrank_of_infinite_dimensional 
(h : ¬FiniteDimensional K V) : finrank K V = 0
（共 82 条，此处仅展示前 30 条）

--- 原说明 ---
If `E / F` is a separable extension, then its separable degree is equal to its d
egree.
When `E / F` is infinite, it means that `Field.Emb F E` has infinitely many elem
ents.
(But the cardinality of `Field.Emb F E` is not equal to `Module.rank F E` in gen
eral!)
-/
theorem finSepDegree_eq_finrank_of_isSeparable [Algebra.IsSeparable F E] :
    finSepDegree F E = finrank F E := by
  wlog hfd : FiniteDimensional F E generalizing E with H
  · rw [finrank_of_infinite_dimensional hfd]
    obtain ⟨L, h, h'⟩ := exists_lt_finrank_of_infinite_dimensional hfd (finSepDegree F E)
    have hd := finSepDegree_mul_finSepDegree_of_isAlgebraic F L E
    rw [H L h] at hd
    by_cases hd' : finSepDegree L E = 0
    · rw [← hd, hd', mul_zero]
    linarith only [h', hd, Nat.le_mul_of_pos_right (finrank F L) (Nat.pos_of_ne_zero hd')]
  rw [← finSepDegree_top F, ← finrank_top F E]
  refine induction_on_adjoin (fun K : IntermediateField F E ↦ finSepDegree F K = finrank F K)
    (by simp_rw [finSepDegree_bot, IntermediateField.finrank_bot]) (fun L x h ↦ ?_) ⊤
  have heq : _ * _ = _ * _ := congr_arg₂ (· * ·) h <|
    (finSepDegree_adjoin_simple_eq_finrank_iff L E x (IsAlgebraic.of_finite L x)).2 <|
      IsSeparable.tower_top L (Algebra.IsSeparable.isSeparable F x)
  set M := L⟮x⟯
  rwa [finSepDegree_mul_finSepDegree_of_isAlgebraic F L M,
    Module.finrank_mul_finrank F L M] at heq

alias Algebra.IsSeparable.finSepDegree_eq := finSepDegree_eq_finrank_of_isSeparable

/-- If `E / F` is a finite extension, then its separable degree is equal to its degree if and
only if it is a separable extension. -/
@[stacks 09HA "The equality condition"]
/-
**Field.finSepDegree_eq_finrank_iff** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：finSepDegree_eq_finrank_iff [FiniteDimensional F E] : finSepDegree F E = f
inrank F E ↔ Algebra.IsSeparable F E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.of_finite`：IsAlgebraic.of_finite (e : A) [Module.Finite R A]
 : IsAlgebraic R e
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.finSepDegree_adjoin_simple_eq_finrank_iff`：finSepDegre
e_adjoin_simple_eq_finrank_iff (α : E) (halg : IsAlgebraic F α) : finSepDegree F
 F⟮α⟯ = finrank F F⟮α⟯ ↔ IsSeparable F α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IntermediateField.finSepDegree_adjoin_simple_le_finrank`：finSepDegree_ad
join_simple_le_finrank (α : E) (halg : IsAlgebraic F α) : finSepDegree F F⟮α⟯ <=
 finrank F F⟮α⟯
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Nat.mul_lt_mul_of_lt_of_le'`：∀ {a c b d : ℕ}, a < c → b ≤ d → 0 < b → a 
* b < c * d
· 使用定理 `Field.finSepDegree_le_finrank`：finSepDegree_le_finrank [FiniteDimensiona
l F E] : finSepDegree F E <= finrank F E
· 使用定理 `Fin.pos'`：∀ {n : ℕ} [Nonempty (Fin n)], 0 < n
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
If `E / F` is a finite extension, then its separable degree is equal to its degr
ee if and
only if it is a separable extension.
-/
theorem finSepDegree_eq_finrank_iff [FiniteDimensional F E] :
    finSepDegree F E = finrank F E ↔ Algebra.IsSeparable F E :=
  ⟨fun heq ↦ ⟨fun x ↦ by
    have halg := IsAlgebraic.of_finite F x
    refine (finSepDegree_adjoin_simple_eq_finrank_iff F E x halg).1 <| le_antisymm
      (finSepDegree_adjoin_simple_le_finrank F E x halg) <| le_of_not_gt fun h ↦ ?_
    have := Nat.mul_lt_mul_of_lt_of_le' h (finSepDegree_le_finrank F⟮x⟯ E) Fin.pos'
    rw [finSepDegree_mul_finSepDegree_of_isAlgebraic F F⟮x⟯ E,
      Module.finrank_mul_finrank F F⟮x⟯ E] at this
    linarith only [heq, this]⟩, fun _ ↦ finSepDegree_eq_finrank_of_isSeparable F E⟩

end Field

/-
**IntermediateField.isSeparable_of_mem_isSeparable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IntermediateField.isSeparable_of_mem_isSeparable {L : IntermediateField F 
E} [Algebra.IsSeparable F L] {x : E} (h : x in L) : IsSeparable F x
参数：h : x in L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.minpoly_eq`：minpoly_eq (x : S) : minpoly K x = minpoly
 K (x : L)
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
-/
lemma IntermediateField.isSeparable_of_mem_isSeparable {L : IntermediateField F E}
    [Algebra.IsSeparable F L] {x : E} (h : x ∈ L) : IsSeparable F x := by
  simpa only [IsSeparable, minpoly_eq] using Algebra.IsSeparable.isSeparable F (K := L) ⟨x, h⟩

/-- `F⟮x⟯ / F` is a separable extension if and only if `x` is a separable element.
As a consequence, any rational function of `x` is also a separable element. -/
/-
**IntermediateField.isSeparable_adjoin_simple_iff_isSeparable** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：IntermediateField.isSeparable_adjoin_simple_iff_isSeparable {x : E} : Alge
bra.IsSeparable F F⟮x⟯ ↔ IsSeparable F x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IntermediateField.isSeparable_of_mem_isSeparable`：IntermediateField.isSe
parable_of_mem_isSeparable {L : IntermediateField F E} [Algebra.IsSeparable F L]
 {x : E} (h : x in L) : IsSeparable F …
· 使用定理 `IntermediateField.mem_adjoin_simple_self`：mem_adjoin_simple_self : α in 
F⟮α⟯
· 使用定理 `IsSeparable.isIntegral`：IsSeparable.isIntegral {x : K} (h : IsSeparable 
F x) : IsIntegral F x
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Field.finSepDegree_eq_finrank_iff`：finSepDegree_eq_finrank_iff [FiniteDi
mensional F E] : finSepDegree F E = finrank F E ↔ Algebra.IsSeparable F E
· 使用定理 `IntermediateField.finSepDegree_adjoin_simple_eq_finrank_iff`：finSepDegre
e_adjoin_simple_eq_finrank_iff (α : E) (halg : IsAlgebraic F α) : finSepDegree F
 F⟮α⟯ = finrank F F⟮α⟯ ↔ IsSeparable F α
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
`F⟮x⟯ / F` is a separable extension if and only if `x` is a separable element.
As a consequence, any rational function of `x` is also a separable element.
-/
theorem IntermediateField.isSeparable_adjoin_simple_iff_isSeparable {x : E} :
    Algebra.IsSeparable F F⟮x⟯ ↔ IsSeparable F x := by
  refine ⟨fun _ ↦ ?_, fun hsep ↦ ?_⟩
  · exact isSeparable_of_mem_isSeparable F E <| mem_adjoin_simple_self F x
  · have h := IsSeparable.isIntegral hsep
    have := adjoin.finiteDimensional h
    rwa [← finSepDegree_eq_finrank_iff,
      finSepDegree_adjoin_simple_eq_finrank_iff F E x h.isAlgebraic]

variable {E K} in
/-- If `K / E / F` is an extension tower such that `E / F` is separable,
`x : K` is separable over `E`, then it's also separable over `F`. -/
/-
**IsSeparable.of_algebra_isSeparable_of_isSeparable** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：IsSeparable.of_algebra_isSeparable_of_isSeparable [Algebra E K] [IsScalarT
ower F E K] [Algebra.IsSeparable F E] {x : K} (hsep : IsSeparable E x) : IsSepar
able F x
参数：hsep : IsSeparable E x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.finiteDimensional_adjoin`：finiteDimensional_adjoin {S 
: Set L} [Finite S] (hS : forall x in S, IsIntegral K x) : FiniteDimensional K (
adjoin K S)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.IsSeparable.isIntegral`：Algebra.IsSeparable.isIntegral [Algebra.
IsSeparable F K] : forall x : K, IsIntegral F x
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Polynomial.map_toSubring`：map_toSubring : (p.toSubring T hp).map (Subrin
g.subtype T) = p
· 使用定理 `IntermediateField.mem_adjoin_simple_self`：mem_adjoin_simple_self : α in 
F⟮α⟯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `isIntegral_trans`：isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx 
: IsIntegral A x) : IsIntegral R x
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsSeparable.isIntegral`：IsSeparable.isIntegral {x : K} (h : IsSeparable 
F x) : IsIntegral F x
· 使用定理 `Polynomial.Separable.of_dvd`：∀ {R : Type u} [inst : CommSemiring R] {f g
 : Polynomial R}, f.Separable → g ∣ f → g.Separable
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `Algebra.isSeparable_tower_bot_of_isSeparable`：Algebra.isSeparable_tower_
bot_of_isSeparable [h : Algebra.IsSeparable F E] : Algebra.IsSeparable F K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`：Intermediat
eField.isSeparable_adjoin_simple_iff_isSeparable {x : E} : Algebra.IsSeparable F
 F⟮x⟯ ↔ IsSeparable F x
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `FiniteDimensional.trans`：trans [FiniteDimensional F K] [FiniteDimensiona
l K A] : FiniteDimensional F A
· 使用定理 `IntermediateField.instIsScalarTowerSubtypeMem_1`：∀ {K : Type u_1} {L : T
ype u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] {S : Interme
diateField K L}   {E : Type u_4} [ins…
· 使用定理 `Field.finSepDegree_mul_finSepDegree_of_isAlgebraic`：finSepDegree_mul_fin
SepDegree_of_isAlgebraic [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebrai
c E K] : finSepDegree F E * finSepDegree…
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
If `K / E / F` is an extension tower such that `E / F` is separable,
`x : K` is separable over `E`, then it's also separable over `F`.
-/
theorem IsSeparable.of_algebra_isSeparable_of_isSeparable [Algebra E K] [IsScalarTower F E K]
    [Algebra.IsSeparable F E] {x : K} (hsep : IsSeparable E x) : IsSeparable F x := by
  set f := minpoly E x with hf
  let E' : IntermediateField F E := adjoin F f.coeffs
  have : FiniteDimensional F E' :=
    finiteDimensional_adjoin fun x _ ↦ Algebra.IsSeparable.isIntegral F x
  let g : E'[X] := f.toSubring E'.toSubring (subset_adjoin F _)
  have h : g.map (algebraMap E' E) = f := f.map_toSubring E'.toSubring (subset_adjoin F _)
  clear_value g
  have hx : x ∈ E'⟮x⟯.restrictScalars F := mem_adjoin_simple_self _ x
  have hzero : aeval x g = 0 := by
    simpa only [← hf, ← h, aeval_map_algebraMap] using minpoly.aeval E x
  have halg : IsIntegral E' x :=
    isIntegral_trans (R := F) (A := E) _ (IsSeparable.isIntegral hsep) |>.tower_top
  simp only [IsSeparable, ← hf, ← h, separable_map] at hsep
  replace hsep := hsep.of_dvd <| minpoly.dvd E' x hzero
  have : Algebra.IsSeparable F E' := Algebra.isSeparable_tower_bot_of_isSeparable F E' E
  have := (isSeparable_adjoin_simple_iff_isSeparable _ _).2 hsep
  have := adjoin.finiteDimensional halg
  have : FiniteDimensional F E'⟮x⟯ := FiniteDimensional.trans F E' E'⟮x⟯
  have := finSepDegree_mul_finSepDegree_of_isAlgebraic F E' E'⟮x⟯
  rw [finSepDegree_eq_finrank_of_isSeparable F E',
    finSepDegree_eq_finrank_of_isSeparable E' E'⟮x⟯,
    Module.finrank_mul_finrank F E' E'⟮x⟯,
    eq_comm, finSepDegree_eq_finrank_iff F E'⟮x⟯] at this
  change Algebra.IsSeparable F (restrictScalars F E'⟮x⟯) at this
  exact isSeparable_of_mem_isSeparable F K hx

/-- If `E / F` and `K / E` are both separable extensions, then `K / F` is also separable. -/
@[stacks 09HB]
/-
**Algebra.IsSeparable.trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsSeparable.trans [Algebra E K] [IsScalarTower F E K] [Algebra.IsS
eparable F E] [Algebra.IsSeparable E K] : Algebra.IsSeparable F K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeparable.of_algebra_isSeparable_of_isSeparable`：IsSeparable.of_algebr
a_isSeparable_of_isSeparable [Algebra E K] [IsScalarTower F E K] [Algebra.IsSepa
rable F E] {x : K} (hsep : IsSeparable …
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x

--- 原说明 ---
If `E / F` and `K / E` are both separable extensions, then `K / F` is also separ
able.
-/
theorem Algebra.IsSeparable.trans [Algebra E K] [IsScalarTower F E K]
    [Algebra.IsSeparable F E] [Algebra.IsSeparable E K] : Algebra.IsSeparable F K :=
  ⟨fun x ↦ IsSeparable.of_algebra_isSeparable_of_isSeparable F
    (Algebra.IsSeparable.isSeparable E x)⟩

/-- If `x` and `y` are both separable elements, then `F⟮x, y⟯ / F` is a separable extension.
As a consequence, any rational function of `x` and `y` is also a separable element. -/
/-
**IntermediateField.isSeparable_adjoin_pair_of_isSeparable** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：IntermediateField.isSeparable_adjoin_pair_of_isSeparable {x y : E} (hx : I
sSeparable F x) (hy : IsSeparable F y) : Algebra.IsSeparable F F⟮x, y⟯
参数：hx : IsSeparable F x；hy : IsSeparable F y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin_simple_adjoin_simple`：adjoin_simple_adjoin_simp
le (β : E) : F⟮α⟯⟮β⟯.restrictScalars F = F⟮α, β⟯
· 使用定理 `IsSeparable.tower_top`：IsSeparable.tower_top {x : E} (h : IsSeparable F 
x) : IsSeparable L x
· 使用定理 `Algebra.IsSeparable.trans`：Algebra.IsSeparable.trans [Algebra E K] [IsSc
alarTower F E K] [Algebra.IsSeparable F E] [Algebra.IsSeparable E K] : Algebra.I
sSeparable F K
· 使用定理 `IntermediateField.instIsScalarTowerSubtypeMem_1`：∀ {K : Type u_1} {L : T
ype u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] {S : Interme
diateField K L}   {E : Type u_4} [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`：Intermediat
eField.isSeparable_adjoin_simple_iff_isSeparable {x : E} : Algebra.IsSeparable F
 F⟮x⟯ ↔ IsSeparable F x

--- 原说明 ---
If `x` and `y` are both separable elements, then `F⟮x, y⟯ / F` is a separable ex
tension.
As a consequence, any rational function of `x` and `y` is also a separable eleme
nt.
-/
theorem IntermediateField.isSeparable_adjoin_pair_of_isSeparable {x y : E}
    (hx : IsSeparable F x) (hy : IsSeparable F y) :
    Algebra.IsSeparable F F⟮x, y⟯ := by
  rw [← adjoin_simple_adjoin_simple]
  replace hy := IsSeparable.tower_top F⟮x⟯ hy
  rw [← isSeparable_adjoin_simple_iff_isSeparable] at hx hy
  exact Algebra.IsSeparable.trans F F⟮x⟯ F⟮x⟯⟮y⟯

namespace Field

variable {F E}

/-- If `x` and `y` are both separable elements, then `x * y` is also a separable element. -/
/-
**Field.isSeparable_mul** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：isSeparable_mul {x y : E} (hx : IsSeparable F x) (hy : IsSeparable F y) : 
IsSeparable F (x * y)
参数：hx : IsSeparable F x；hy : IsSeparable F y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IntermediateField.isSeparable_of_mem_isSeparable`：IntermediateField.isSe
parable_of_mem_isSeparable {L : IntermediateField F E} [Algebra.IsSeparable F L]
 {x : E} (h : x in L) : IsSeparable F …
· 使用定理 `IntermediateField.isSeparable_adjoin_pair_of_isSeparable`：IntermediateFi
eld.isSeparable_adjoin_pair_of_isSeparable {x y : E} (hx : IsSeparable F x) (hy 
: IsSeparable F y) : Algebra.IsSeparable F F⟮x…
· 使用定理 `IntermediateField.mul_mem`：∀ {K : Type u_1} {L : Type u_2} [inst : Field
 K] [inst_1 : Field L] [inst_2 : Algebra K L] (S : IntermediateField K L)   {x y
 : L}, x ∈ S → …
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S

--- 原说明 ---
If `x` and `y` are both separable elements, then `x * y` is also a separable ele
ment.
-/
theorem isSeparable_mul {x y : E} (hx : IsSeparable F x) (hy : IsSeparable F y) :
    IsSeparable F (x * y) :=
  haveI := isSeparable_adjoin_pair_of_isSeparable F E hx hy
  isSeparable_of_mem_isSeparable F E <| F⟮x, y⟯.mul_mem (subset_adjoin F _ (.inl rfl))
    (subset_adjoin F _ (.inr rfl))

/-- If `x` and `y` are both separable elements, then `x + y` is also a separable element. -/
/-
**Field.isSeparable_add** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：isSeparable_add {x y : E} (hx : IsSeparable F x) (hy : IsSeparable F y) : 
IsSeparable F (x + y)
参数：hx : IsSeparable F x；hy : IsSeparable F y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IntermediateField.isSeparable_of_mem_isSeparable`：IntermediateField.isSe
parable_of_mem_isSeparable {L : IntermediateField F E} [Algebra.IsSeparable F L]
 {x : E} (h : x in L) : IsSeparable F …
· 使用定理 `IntermediateField.isSeparable_adjoin_pair_of_isSeparable`：IntermediateFi
eld.isSeparable_adjoin_pair_of_isSeparable {x y : E} (hx : IsSeparable F x) (hy 
: IsSeparable F y) : Algebra.IsSeparable F F⟮x…
· 使用定理 `IntermediateField.add_mem`：∀ {K : Type u_1} {L : Type u_2} [inst : Field
 K] [inst_1 : Field L] [inst_2 : Algebra K L] (S : IntermediateField K L)   {x y
 : L}, x ∈ S → …
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S

--- 原说明 ---
If `x` and `y` are both separable elements, then `x + y` is also a separable ele
ment.
-/
theorem isSeparable_add {x y : E} (hx : IsSeparable F x) (hy : IsSeparable F y) :
    IsSeparable F (x + y) :=
  haveI := isSeparable_adjoin_pair_of_isSeparable F E hx hy
  isSeparable_of_mem_isSeparable F E <| F⟮x, y⟯.add_mem (subset_adjoin F _ (.inl rfl))
    (subset_adjoin F _ (.inr rfl))

/-- If `x` is a separable elements, then `-x` is also a separable element. -/
/-
**Field.isSeparable_neg** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：isSeparable_neg {x : E} (hx : IsSeparable F x) : IsSeparable F (-x)
参数：hx : IsSeparable F x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IntermediateField.isSeparable_of_mem_isSeparable`：IntermediateField.isSe
parable_of_mem_isSeparable {L : IntermediateField F E} [Algebra.IsSeparable F L]
 {x : E} (h : x in L) : IsSeparable F …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`：Intermediat
eField.isSeparable_adjoin_simple_iff_isSeparable {x : E} : Algebra.IsSeparable F
 F⟮x⟯ ↔ IsSeparable F x
· 使用定理 `IntermediateField.neg_mem`：∀ {K : Type u_1} {L : Type u_2} [inst : Field
 K] [inst_1 : Field L] [inst_2 : Algebra K L] (S : IntermediateField K L)   {x :
 L}, x ∈ S → -x…
· 使用定理 `IntermediateField.mem_adjoin_simple_self`：mem_adjoin_simple_self : α in 
F⟮α⟯

--- 原说明 ---
If `x` is a separable elements, then `-x` is also a separable element.
-/
theorem isSeparable_neg {x : E} (hx : IsSeparable F x) :
    IsSeparable F (-x) :=
  haveI := (isSeparable_adjoin_simple_iff_isSeparable F E).2 hx
  isSeparable_of_mem_isSeparable F E <| F⟮x⟯.neg_mem <| mem_adjoin_simple_self F x

/-- If `x` and `y` are both separable elements, then `x - y` is also a separable element. -/
/-
**Field.isSeparable_sub** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：isSeparable_sub {x y : E} (hx : IsSeparable F x) (hy : IsSeparable F y) : 
IsSeparable F (x - y)
参数：hx : IsSeparable F x；hy : IsSeparable F y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IntermediateField.isSeparable_of_mem_isSeparable`：IntermediateField.isSe
parable_of_mem_isSeparable {L : IntermediateField F E} [Algebra.IsSeparable F L]
 {x : E} (h : x in L) : IsSeparable F …
· 使用定理 `IntermediateField.isSeparable_adjoin_pair_of_isSeparable`：IntermediateFi
eld.isSeparable_adjoin_pair_of_isSeparable {x y : E} (hx : IsSeparable F x) (hy 
: IsSeparable F y) : Algebra.IsSeparable F F⟮x…
· 使用定理 `IntermediateField.sub_mem`：∀ {K : Type u_1} {L : Type u_2} [inst : Field
 K] [inst_1 : Field L] [inst_2 : Algebra K L] (S : IntermediateField K L)   {x y
 : L}, x ∈ S → …
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S

--- 原说明 ---
If `x` and `y` are both separable elements, then `x - y` is also a separable ele
ment.
-/
theorem isSeparable_sub {x y : E} (hx : IsSeparable F x) (hy : IsSeparable F y) :
    IsSeparable F (x - y) :=
  haveI := isSeparable_adjoin_pair_of_isSeparable F E hx hy
  isSeparable_of_mem_isSeparable F E <| F⟮x, y⟯.sub_mem (subset_adjoin F _ (.inl rfl))
    (subset_adjoin F _ (.inr rfl))

/-- If `x` is a separable element, then `x⁻¹` is also a separable element. -/
/-
**Field.isSeparable_inv** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：isSeparable_inv {x : E} (hx : IsSeparable F x) : IsSeparable F x⁻¹
参数：hx : IsSeparable F x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IntermediateField.isSeparable_of_mem_isSeparable`：IntermediateField.isSe
parable_of_mem_isSeparable {L : IntermediateField F E} [Algebra.IsSeparable F L]
 {x : E} (h : x in L) : IsSeparable F …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`：Intermediat
eField.isSeparable_adjoin_simple_iff_isSeparable {x : E} : Algebra.IsSeparable F
 F⟮x⟯ ↔ IsSeparable F x
· 使用定理 `IntermediateField.inv_mem`：∀ {K : Type u_1} {L : Type u_2} [inst : Field
 K] [inst_1 : Field L] [inst_2 : Algebra K L] (S : IntermediateField K L)   {x :
 L}, x ∈ S → x⁻…
· 使用定理 `IntermediateField.mem_adjoin_simple_self`：mem_adjoin_simple_self : α in 
F⟮α⟯

--- 原说明 ---
If `x` is a separable element, then `x⁻¹` is also a separable element.
-/
theorem isSeparable_inv {x : E} (hx : IsSeparable F x) : IsSeparable F x⁻¹ :=
  haveI := (isSeparable_adjoin_simple_iff_isSeparable F E).2 hx
  isSeparable_of_mem_isSeparable F E <| F⟮x⟯.inv_mem <| mem_adjoin_simple_self F x

end Field

/-- A field is a perfect field (which means that any irreducible polynomial is separable)
if and only if every separable degree one polynomial splits. -/
/-
**perfectField_iff_splits_of_natSepDegree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：perfectField_iff_splits_of_natSepDegree_eq_one (F : Type*) [Field F] : Per
fectField F ↔ forall f : F[X], f.natSepDegree = 1 -> Splits f
参数：F : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natSepDegree_zero`：natSepDegree_zero : (0 : F[X]).natSepDegre
e = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `UniqueFactorizationMonoid.factors_prod`：factors_prod {a : α} (ane0 : a !
= 0) : Associated (factors a).prod a
· 使用定理 `Polynomial.Splits.mul`：∀ {R : Type u_1} [inst : Semiring R] {f g : Polyn
omial R}, f.Splits → g.Splits → (f * g).Splits
· 使用定理 `Polynomial.Splits.multisetProd`：∀ {R : Type u_1} [inst : CommSemiring R]
 {m : Multiset (Polynomial R)}, (∀ f ∈ m, f.Splits) → m.prod.Splits
· 使用定理 `Polynomial.natSepDegree_le_of_dvd`：natSepDegree_le_of_dvd (g : F[X]) (h1
 : f ∣ g) (h2 : g != 0) : f.natSepDegree <= g.natSepDegree
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_factors`：dvd_of_mem_factors {p a : 
α} (h : p in factors a) : p ∣ a
· 使用定理 `Polynomial.Splits.of_natDegree_le_one`：∀ {R : Type u_1} [inst : Division
Semiring R] {f : Polynomial R}, f.natDegree ≤ 1 → f.Splits
· 使用定理 `Polynomial.Separable.natSepDegree_eq_natDegree`：∀ {F : Type u} [inst : F
ield F] {f : Polynomial F}, f.Separable → f.natSepDegree = f.natDegree
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_factor`：irreducible_of_factor {
a : α} : forall x : α, x in factors a -> Irreducible x
· 使用定理 `IsUnit.splits`：∀ {R : Type u_1} [inst : Semiring R] [NoZeroDivisors R] {
f : Polynomial R}, IsUnit f → f.Splits
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用引理 `ExpChar.exists`：ExpChar.exists [Ring R] [IsDomain R] : exists q, ExpChar
 R q
· 使用引理 `PerfectRing.ofSurjective`：PerfectRing.ofSurjective (R : Type*) (p : Nat)
 [CommRing R] [ExpChar R p] [IsReduced R] (h : Surjective <| frobenius R p) : Pe
rfectRing R p
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Polynomial.Splits.exists_eval_eq_zero`：∀ {R : Type u_1} [inst : CommRing
 R] {f : Polynomial R}, f.Splits → f.degree ≠ 0 → ∃ a, Polynomial.eval a f = 0
· 使用定理 `Polynomial.natSepDegree_X_pow_char_pow_sub_C`：natSepDegree_X_pow_char_po
w_sub_C (q : Nat) [ExpChar F q] (n : Nat) (y : F) : (X ^ q ^ n - C y).natSepDegr
ee = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
A field is a perfect field (which means that any irreducible polynomial is separ
able)
if and only if every separable degree one polynomial splits.
-/
theorem perfectField_iff_splits_of_natSepDegree_eq_one (F : Type*) [Field F] :
    PerfectField F ↔ ∀ f : F[X], f.natSepDegree = 1 → Splits f := by
  refine ⟨fun ⟨h⟩ f hf ↦ ?_, fun h ↦ ?_⟩
  · have hf0 : f ≠ 0 := by aesop
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hf0
    rw [← hu]
    refine (Splits.multisetProd fun g hg ↦ ?_).mul u.isUnit.splits
    specialize h (UniqueFactorizationMonoid.irreducible_of_factor g hg)
    have key := natSepDegree_le_of_dvd g f (UniqueFactorizationMonoid.dvd_of_mem_factors hg) hf0
    rw [h.natSepDegree_eq_natDegree, hf] at key
    exact Splits.of_natDegree_le_one key
  obtain ⟨p, _⟩ := ExpChar.exists F
  have := PerfectRing.ofSurjective F p fun x ↦ by
    obtain ⟨y, hy⟩ := Splits.exists_eval_eq_zero
      (h _ (pow_one p ▸ natSepDegree_X_pow_char_pow_sub_C p 1 x))
      ((degree_X_pow_sub_C (expChar_pos F p) x).symm ▸ Nat.cast_pos.2 (expChar_pos F p)).ne'
    exact ⟨y, by rwa [eval_sub, eval_X_pow, eval_C, sub_eq_zero] at hy⟩
  exact PerfectRing.toPerfectField F p

variable {E K} in
/-
**PerfectField.splits_of_natSepDegree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PerfectField.splits_of_natSepDegree_eq_one [PerfectField K] {f : E[X]} (i 
: E ->+* K) (hf : f.natSepDegree = 1) : (f.map i).Splits
参数：i : E ->+* K；hf : f.natSepDegree = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `perfectField_iff_splits_of_natSepDegree_eq_one`：perfectField_iff_splits_
of_natSepDegree_eq_one (F : Type*) [Field F] : PerfectField F ↔ forall f : F[X],
 f.natSepDegree = 1 -> Splits f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natSepDegree_map`：natSepDegree_map (f : E[X]) (i : E ->+* K) 
: (f.map i).natSepDegree = f.natSepDegree
-/
theorem PerfectField.splits_of_natSepDegree_eq_one [PerfectField K] {f : E[X]}
    (i : E →+* K) (hf : f.natSepDegree = 1) : (f.map i).Splits :=
  (perfectField_iff_splits_of_natSepDegree_eq_one K).mp ‹_› _ (natSepDegree_map K f i ▸ hf)
