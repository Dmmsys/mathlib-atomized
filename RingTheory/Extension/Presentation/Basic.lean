/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jung Tao Cheng, Christian Merten, Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!

# Presentations of algebras

A presentation of an `R`-algebra `S` is a distinguished family of generators and relations.

## Main definition

- `Algebra.Presentation`: A presentation of an `R`-algebra `S` is a family of
  generators with
  1. `rels`: The type of relations.
  2. `relation : relations → MvPolynomial vars R`: The assignment of
     each relation to a polynomial in the generators.
- `Algebra.Presentation.IsFinite`: A presentation is called finite if both variables and relations
  are finite.
- `Algebra.Presentation.dimension`: The dimension of a presentation is the number of generators
  minus the number of relations.

We also give constructors for localization, base change and composition.

## TODO

- Define `Hom`s of presentations.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry"
in June 2024.

-/

@[expose] public section

universe t w u v

open TensorProduct MvPolynomial

variable (R : Type u) (S : Type v) (ι : Type w) (σ : Type t) [CommRing R] [CommRing S] [Algebra R S]

/--
A presentation of an `R`-algebra `S` is a family of
generators with `σ → MvPolynomial ι R`: The assignment of
each relation to a polynomial in the generators.
-/
/-
**Algebra.Presentation** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u) →   (S : Type v) →     Type w → Type t → [inst : CommRing R] 
→ [inst_1 : CommRing S] → [Algebra R S] → Type (max (max (max t u) v) w)
参数：max (max t u) v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A presentation of an `R`-algebra `S` is a family of
generators with `σ → MvPolynomial ι R`: The assignment of
each relation to a polynomial in the generators.
-/
structure Algebra.Presentation extends Algebra.Generators R S ι where
  /-- The assignment of each relation to a polynomial in the generators. -/
  relation : σ → toGenerators.Ring
  /-- The relations span the kernel of the canonical map. -/
  span_range_relation_eq_ker :
    Ideal.span (Set.range relation) = toGenerators.ker

namespace Algebra.Presentation

variable {R S ι σ}
variable (P : Presentation R S ι σ)

@[simp]
/-
**Algebra.Presentation.aeval_val_relation** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Pre
sentation`。
形式化陈述：aeval_val_relation (i) : aeval P.val (P.relation i) = 0
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用引理 `Algebra.Generators.ker_eq_ker_aeval_val`：ker_eq_ker_aeval_val : P.ker = 
RingHom.ker (aeval P.val)
· 使用定理 `Algebra.Presentation.span_range_relation_eq_ker`：∀ {R : Type u} {S : Typ
e v} {ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2
 : Algebra R S]   (self : Algebra.Pre…
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
-/
lemma aeval_val_relation (i) : aeval P.val (P.relation i) = 0 := by
  rw [← RingHom.mem_ker, ← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker]
  exact Ideal.subset_span ⟨i, rfl⟩
/-
**Algebra.Presentation.relation_mem_ker** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Prese
ntation`。
形式化陈述：relation_mem_ker (i) : P.relation i in P.ker
参数：i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.Presentation.span_range_relation_eq_ker`：∀ {R : Type u} {S : Typ
e v} {ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2
 : Algebra R S]   (self : Algebra.Pre…
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
-/
lemma relation_mem_ker (i) : P.relation i ∈ P.ker := by
  rw [← P.span_range_relation_eq_ker]
  apply Ideal.subset_span
  use i

/-- The polynomial algebra w.r.t. a family of generators modulo a family of relations. -/
/-
**Algebra.Presentation.Quotient** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Presentation`
。
形式化陈述：{R : Type u} →   {S : Type v} →     {ι : Type w} →       {σ : Type t} →   
      [inst : CommRing R] →           [inst_1 : CommRing S] → [inst_2 : Algebra 
R S] → Algebra.Presentation R S ι σ → Type (max w u)
参数：max w u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polynomial algebra w.r.t. a family of generators modulo a family of relation
s.
-/
protected abbrev Quotient : Type (max w u) := P.Ring ⧸ P.ker

/-- `P.Quotient` is `P.Ring`-isomorphic to `S` and in particular `R`-isomorphic to `S`. -/
/-
**Algebra.Presentation.quotientEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Presenta
tion`。
形式化陈述：quotientEquiv : P.Quotient ≃ₐ[P.Ring] S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P.Quotient` is `P.Ring`-isomorphic to `S` and in particular `R`-isomorphic to `
S`.
-/
noncomputable def quotientEquiv : P.Quotient ≃ₐ[P.Ring] S :=
  Ideal.quotientKerAlgEquivOfRightInverse (f := Algebra.ofId P.Ring S) (g := P.σ) <| fun x ↦ by
    rw [Algebra.ofId_apply, P.algebraMap_apply, P.aeval_val_σ]

@[simp]
/-
**Algebra.Presentation.quotientEquiv_mk** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Prese
ntation`。
形式化陈述：quotientEquiv_mk (p : P.Ring) : P.quotientEquiv p = algebraMap P.Ring S p
参数：p : P.Ring。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma quotientEquiv_mk (p : P.Ring) : P.quotientEquiv p = algebraMap P.Ring S p :=
  rfl

@[simp]
/-
**Algebra.Presentation.quotientEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Pre
sentation`。
形式化陈述：quotientEquiv_symm (x : S) : P.quotientEquiv.symm x = P.σ x
参数：x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quotientEquiv_symm (x : S) : P.quotientEquiv.symm x = P.σ x :=
  rfl

set_option linter.unusedVariables false in
/--
Dimension of a presentation defined as the cardinality of the generators
minus the cardinality of the relations.

Note: this definition is completely non-sensical for non-finite presentations and
even then for this to make sense, you should assume that the presentation
is a complete intersection.
-/
@[nolint unusedArguments]
/-
**Algebra.Presentation.dimension** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Presentation
`。
形式化陈述：dimension (P : Presentation R S ι σ) : Nat
参数：P : Presentation R S ι σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dimension of a presentation defined as the cardinality of the generators
minus the cardinality of the relations.

Note: this definition is completely non-sensical for non-finite presentations an
d
even then for this to make sense, you should assume that the presentation
is a complete intersection.
-/
noncomputable def dimension (P : Presentation R S ι σ) : ℕ :=
  Nat.card ι - Nat.card σ
/-
**Algebra.Presentation.fg_ker** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Presentation`。
形式化陈述：fg_ker [Finite σ] : P.ker.FG
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Algebra.Presentation.span_range_relation_eq_ker`：∀ {R : Type u} {S : Typ
e v} {ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2
 : Algebra R S]   (self : Algebra.Pre…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fg_ker [Finite σ] : P.ker.FG := by
  use (Set.finite_range P.relation).toFinset
  simp [span_range_relation_eq_ker]

/-- If a presentation is finite, the corresponding quotient is
of finite presentation. -/
/-
**Algebra.Presentation.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Presentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a presentation is finite, the corresponding quotient is
of finite presentation.
-/
instance [Finite σ] [Finite ι] : FinitePresentation R P.Quotient :=
  FinitePresentation.quotient P.fg_ker
/-
**Algebra.Presentation.finitePresentation_of_isFinite** 是 Mathlib 中的一个引理，位于命名空间 
`Algebra.Presentation`。
形式化陈述：finitePresentation_of_isFinite [Finite σ] [Finite ι] (P : Presentation R S
 ι σ) : FinitePresentation R S
参数：P : Presentation R S ι σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FinitePresentation.equiv`：equiv [FinitePresentation R A] (e : A 
≃ₐ[R] B) : FinitePresentation R B
· 使用定理 `Algebra.Presentation.instFinitePresentationQuotientOfFinite`：∀ {R : Type
 u} {S : Type v} {ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRin
g S] [inst_2 : Algebra R S]   (P : Algebra.Presen…
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.Generators.instIsScalarTowerRing`：∀ {R : Type u} {S : Type v} {ι
 : Type w} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (P
 : Algebra.Generators R S ι) {…
-/
lemma finitePresentation_of_isFinite [Finite σ] [Finite ι] (P : Presentation R S ι σ) :
    FinitePresentation R S :=
  FinitePresentation.equiv (P.quotientEquiv.restrictScalars R)

variable (R S) in
/-
**Algebra.Presentation.exists_presentation_fin** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a.Presentation`。
形式化陈述：exists_presentation_fin [FinitePresentation R S] : exists n m, Nonempty (P
resentation R S (Fin n) (Fin m))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FinitePresentation.out`：∀ {R : Type w₁} {A : Type w₂} {inst : Co
mmSemiring R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.Fin
itePresentation R A]…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.fg_iff_exists_fin_generating_family`：fg_iff_exists_fin_generat
ing_family {N : Submodule R M} : N.FG ↔ exists (n : Nat) (s : Fin n -> M), span 
R (range s) = N
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma exists_presentation_fin [FinitePresentation R S] :
    ∃ n m, Nonempty (Presentation R S (Fin n) (Fin m)) :=
  letI H := FinitePresentation.out (R := R) (A := S)
  letI n : ℕ := H.choose
  letI f : MvPolynomial (Fin n) R →ₐ[R] S := H.choose_spec.choose
  haveI hf : Function.Surjective f := H.choose_spec.choose_spec.1
  haveI hf' : (RingHom.ker f).FG := H.choose_spec.choose_spec.2
  letI H' := Submodule.fg_iff_exists_fin_generating_family.mp hf'
  let m : ℕ := H'.choose
  let v : Fin m → MvPolynomial (Fin n) R := H'.choose_spec.choose
  have hv : Ideal.span (Set.range v) = RingHom.ker f := H'.choose_spec.choose_spec
  ⟨n, m,
    ⟨{__ := Generators.ofSurjective (fun x ↦ f (.X x)) (by convert! hf; ext; simp)
      relation := v
      span_range_relation_eq_ker := hv.trans (by congr; ext; simp) }⟩⟩

variable (R S) in
/-- The index of generators to `ofFinitePresentation`. -/
noncomputable
/-
**Algebra.Presentation.ofFinitePresentationVars** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
ra.Presentation`。
形式化陈述：ofFinitePresentationVars [FinitePresentation R S] : Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.Presentation.exists_presentation_fin`：exists_presentation_fin [F
initePresentation R S] : exists n m, Nonempty (Presentation R S (Fin n) (Fin m))
-/
def ofFinitePresentationVars [FinitePresentation R S] : ℕ :=
  (exists_presentation_fin R S).choose

variable (R S) in
/-- The index of relations to `ofFinitePresentation`. -/
noncomputable
/-
**Algebra.Presentation.ofFinitePresentationRels** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
ra.Presentation`。
形式化陈述：ofFinitePresentationRels [FinitePresentation R S] : Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.Presentation.exists_presentation_fin`：exists_presentation_fin [F
initePresentation R S] : exists n m, Nonempty (Presentation R S (Fin n) (Fin m))
-/
def ofFinitePresentationRels [FinitePresentation R S] : ℕ :=
  (exists_presentation_fin R S).choose_spec.choose

variable (R S) in
/-- An arbitrary choice of a finite presentation of a finitely presented algebra. -/
noncomputable
/-
**Algebra.Presentation.ofFinitePresentation** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.P
resentation`。
形式化陈述：ofFinitePresentation [FinitePresentation R S] : Presentation R S (Fin (ofF
initePresentationVars R S)) (Fin (ofFinitePresentationRels R S))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.Presentation.exists_presentation_fin`：exists_presentation_fin [F
initePresentation R S] : exists n m, Nonempty (Presentation R S (Fin n) (Fin m))
-/
def ofFinitePresentation [FinitePresentation R S] :
    Presentation R S (Fin (ofFinitePresentationVars R S)) (Fin (ofFinitePresentationRels R S)) :=
  (exists_presentation_fin R S).choose_spec.choose_spec.some

section Construction

/-- Transport a presentation along an algebra isomorphism. -/
@[simps toGenerators relation]
/-
**Algebra.Presentation.ofAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Presentatio
n`。
形式化陈述：ofAlgEquiv (P : Presentation R S ι σ) {T : Type*} [CommRing T] [Algebra R 
T] (e : S ≃ₐ[R] T) : Presentation R T ι σ where __
参数：P : Presentation R S ι σ；e : S ≃ₐ[R] T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport a presentation along an algebra isomorphism.
-/
noncomputable def ofAlgEquiv (P : Presentation R S ι σ) {T : Type*} [CommRing T] [Algebra R T]
    (e : S ≃ₐ[R] T) :
    Presentation R T ι σ where
  __ := Generators.ofAlgEquiv P.toGenerators e
  relation i := P.relation i
  span_range_relation_eq_ker := by simp [P.span_range_relation_eq_ker]

@[simp]
/-
**Algebra.Presentation.dimension_ofAlgEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.P
resentation`。
形式化陈述：dimension_ofAlgEquiv (P : Presentation R S ι σ) {T : Type*} [CommRing T] [
Algebra R T] (e : S ≃ₐ[R] T) : (P.ofAlgEquiv e).dimension = P.dimension
参数：P : Presentation R S ι σ；e : S ≃ₐ[R] T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dimension_ofAlgEquiv (P : Presentation R S ι σ) {T : Type*} [CommRing T] [Algebra R T]
    (e : S ≃ₐ[R] T) : (P.ofAlgEquiv e).dimension = P.dimension :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- If `algebraMap R S` is bijective, the empty generators are a presentation with no relations. -/
/-
**Algebra.Presentation.ofBijectiveAlgebraMap** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.
Presentation`。
形式化陈述：ofBijectiveAlgebraMap (h : Function.Bijective (algebraMap R S)) : Presenta
tion R S PEmpty.{w + 1} PEmpty.{t + 1} where __
参数：h : Function.Bijective (algebraMap R S)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `algebraMap R S` is bijective, the empty generators are a presentation with n
o relations.
-/
noncomputable def ofBijectiveAlgebraMap (h : Function.Bijective (algebraMap R S)) :
    Presentation R S PEmpty.{w + 1} PEmpty.{t + 1} where
  __ := Generators.ofSurjectiveAlgebraMap h.surjective
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    simp only [Set.range_eq_empty, Ideal.span_empty]
    symm
    rw [← RingHom.injective_iff_ker_eq_bot]
    change Function.Injective (aeval PEmpty.elim)
    rw [aeval_injective_iff_of_isEmpty]
    exact h.injective
/-
**Algebra.Presentation.ofBijectiveAlgebraMap_dimension** 是 Mathlib 中的一个引理，位于命名空间
 `Algebra.Presentation`。
形式化陈述：ofBijectiveAlgebraMap_dimension (h : Function.Bijective (algebraMap R S)) 
: (ofBijectiveAlgebraMap h).dimension = 0
参数：h : Function.Bijective (algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofBijectiveAlgebraMap_dimension (h : Function.Bijective (algebraMap R S)) :
    (ofBijectiveAlgebraMap h).dimension = 0 := by
  simp [dimension]

variable (R) in
/-- The canonical `R`-presentation of `R` with no generators and no relations. -/
/-
**Algebra.Presentation.id** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Presentation`。
形式化陈述：id : Presentation R R PEmpty.{w + 1} PEmpty.{t + 1}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)

--- 原说明 ---
The canonical `R`-presentation of `R` with no generators and no relations.
-/
noncomputable def id : Presentation R R PEmpty.{w + 1} PEmpty.{t + 1} :=
  ofBijectiveAlgebraMap Function.bijective_id
/-
**Algebra.Presentation.id_dimension** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Presentat
ion`。
形式化陈述：id_dimension : (Presentation.id R).dimension = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.Presentation.ofBijectiveAlgebraMap_dimension`：ofBijectiveAlgebra
Map_dimension (h : Function.Bijective (algebraMap R S)) : (ofBijectiveAlgebraMap
 h).dimension = 0
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
lemma id_dimension : (Presentation.id R).dimension = 0 :=
  ofBijectiveAlgebraMap_dimension (R := R) Function.bijective_id

section Localization

variable (r : R) [IsLocalization.Away r S]

open IsLocalization.Away

/-
**Algebra.Presentation._root_.Algebra.Generators.ker_localizationAway** 是 Mathli
b 中的一个引理，位于命名空间 `Algebra.Presentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Algebra.Generators.ker_localizationAway :
    (Generators.localizationAway S r).ker = Ideal.span { C r * X () - 1 } := by
  have : aeval (S₁ := S) (Generators.localizationAway S r).val =
      (mvPolynomialQuotientEquiv S r).toAlgHom.comp
        (Ideal.Quotient.mkₐ R (Ideal.span {C r * X () - 1})) := by
    ext x
    simp only [aeval_X, Generators.localizationAway_val, AlgHom.coe_comp,
      AlgEquiv.coe_toAlgHom, Ideal.Quotient.mkₐ_eq_mk, Function.comp_apply]
    rw [IsLocalization.Away.mvPolynomialQuotientEquiv_apply, aeval_X]
  rw [Generators.ker_eq_ker_aeval_val, this, ← RingHom.ker_coe_toRingHom, AlgHom.comp_toRingHom,
    ← RingHom.comap_ker]
  simp only [AlgEquiv.toAlgHom_toRingHom]
  change Ideal.comap _ (RingHom.ker (mvPolynomialQuotientEquiv S r)) = Ideal.span {C r * X () - 1}
  simp [RingHom.ker_equiv, ← RingHom.ker_eq_comap_bot]

variable (S) in
/-- If `S` is the localization of `R` away from `r`, we can construct a natural
presentation of `S` as `R`-algebra with a single generator `X` and the relation `r * X - 1 = 0`. -/
@[simps relation]
/-
**Algebra.Presentation.localizationAway** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Prese
ntation`。
形式化陈述：localizationAway : Presentation R S Unit Unit where toGenerators
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is the localization of `R` away from `r`, we can construct a natural
presentation of `S` as `R`-algebra with a single generator `X` and the relation 
`r * X - 1 = 0`.
-/
noncomputable def localizationAway : Presentation R S Unit Unit where
  toGenerators := Generators.localizationAway S r
  relation _ := C r * X () - 1
  span_range_relation_eq_ker := by
    simp only [Set.range_const]
    exact (Generators.ker_localizationAway r).symm

@[simp]
/-
**Algebra.Presentation.localizationAway_dimension_zero** 是 Mathlib 中的一个引理，位于命名空间
 `Algebra.Presentation`。
形式化陈述：localizationAway_dimension_zero : (localizationAway S r).dimension = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma localizationAway_dimension_zero : (localizationAway S r).dimension = 0 := by
  simp [Presentation.dimension]
/-
**Algebra.Presentation._root_.Algebra.Generators.C_mul_X_sub_one_mem_ker** 是 Mat
hlib 中的一个引理，位于命名空间 `Algebra.Presentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Algebra.Generators.C_mul_X_sub_one_mem_ker :
    C r * X () - 1 ∈ (Generators.localizationAway S r).ker :=
  (Presentation.localizationAway S r).relation_mem_ker ()

end Localization

section BaseChange

variable (T) [CommRing T] [Algebra R T] (P : Presentation R S ι σ)

/-
**Algebra.Presentation.span_range_relation_eq_ker_baseChange** 是 Mathlib 中的一个引理，
位于命名空间 `Algebra.Presentation`。
形式化陈述：span_range_relation_eq_ker_baseChange : Ideal.span (Set.range fun i => (Mv
Polynomial.map (algebraMap R T)) (P.relation i)) = RingHom.ker (aeval (S₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用引理 `Algebra.Presentation.aeval_val_relation`：aeval_val_relation (i) : aeval 
P.val (P.relation i) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MvPolynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : σ -> B) (p 
: MvPolynomial σ R) : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `MvPolynomial.map_aeval`：map_aeval {B : Type*} [CommSemiring B] (g : σ ->
 S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R) : φ (aeval g p) = eval₂Hom (φ.comp (
algebraMap R…
· 使用定理 `AlgHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom
 = f
· 使用定理 `RingHom.coe_coe`：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β
] (f : F) : ((f : α ->+* β) : α -> β) = f
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.Generators.instIsScalarTowerRing`：∀ {R : Type u} {S : Type v} {ι
 : Type w} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (P
 : Algebra.Generators R S ι) {…
· 使用引理 `Algebra.TensorProduct.lTensor_ker`：Algebra.TensorProduct.lTensor_ker (hg
 : Function.Surjective g) : RingHom.ker (map (AlgHom.id R A) g) = (RingHom.ker g
).map (Algebra.TensorPr…
· 使用引理 `Algebra.Generators.algebraMap_surjective`：algebraMap_surjective : Functi
on.Surjective (algebraMap P.Ring S)
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `MvPolynomial.induction_on`：induction_on {motive : MvPolynomial σ R -> Pr
op} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (add : forall p q, motiv
e p -> motive q…
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用定理 `MvPolynomial.algebraMap_eq`：algebraMap_eq : algebraMap R (MvPolynomial σ
 R) = C
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
（共 62 条，此处仅展示前 30 条）
-/
lemma span_range_relation_eq_ker_baseChange :
    Ideal.span (Set.range fun i ↦ (MvPolynomial.map (algebraMap R T)) (P.relation i)) =
      RingHom.ker (aeval (S₁ := T ⊗[R] S) (P.baseChange T).val) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x ⟨y, hy⟩
    have Z := aeval_val_relation P y
    apply_fun TensorProduct.includeRight (R := R) (A := T) at Z
    rw [map_zero] at Z
    simp only [SetLike.mem_coe, RingHom.mem_ker, ← Z, ← hy,
      TensorProduct.includeRight_apply]
    rw [aeval_map_algebraMap T (P.baseChange T).val (P.relation y)]
    change _ = TensorProduct.includeRight.toRingHom _
    rw [map_aeval, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      TensorProduct.includeRight.comp_algebraMap]
    rfl
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have H := Algebra.TensorProduct.lTensor_ker (A := T) (IsScalarTower.toAlgHom R P.Ring S)
      P.algebraMap_surjective
    let e := MvPolynomial.algebraTensorAlgEquiv (R := R) (σ := ι) (A := T)
    have H' : e.symm x ∈ RingHom.ker (TensorProduct.map (AlgHom.id R T)
        (IsScalarTower.toAlgHom R P.Ring S)) := by
      rw [RingHom.mem_ker, ← hx]
      clear hx
      induction x using MvPolynomial.induction_on with
      | C a =>
        simp only [algHom_C, TensorProduct.algebraMap_apply,
          algebraMap_self, RingHom.id_apply, e]
        rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
        simp only [TensorProduct.algebraMap_apply, algebraMap_self, RingHom.id_apply,
          TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_one]
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p i hp => simp [hp, e]
    rw [H] at H'
    replace H' : e.symm x ∈ Ideal.map TensorProduct.includeRight P.ker := H'
    rw [← P.span_range_relation_eq_ker, ← Ideal.mem_comap, ← Ideal.comap_coe,
      ← AlgEquiv.toRingEquiv_toRingHom, Ideal.comap_coe, AlgEquiv.symm_toRingEquiv,
      Ideal.comap_symm, ← Ideal.map_coe, ← Ideal.map_coe _ (Ideal.span _), Ideal.map_map,
      Ideal.map_span, ← Set.range_comp, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
      RingHom.coe_coe] at H'
    convert! H'
    simp [e]

/-- If `P` is a presentation of `S` over `R` and `T` is an `R`-algebra, we
obtain a natural presentation of `T ⊗[R] S` over `T`. -/
@[simps relation]
noncomputable
/-
**Algebra.Presentation.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Presentatio
n`。
形式化陈述：baseChange : Presentation T (T otimes[R] S) ι σ where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.Presentation.span_range_relation_eq_ker_baseChange`：span_range_r
elation_eq_ker_baseChange : Ideal.span (Set.range fun i => (MvPolynomial.map (al
gebraMap R T)) (P.relation i)) = RingHom.ker (ae…
-/
def baseChange : Presentation T (T ⊗[R] S) ι σ where
  __ := P.toGenerators.baseChange T
  relation i := MvPolynomial.map (algebraMap R T) (P.relation i)
  span_range_relation_eq_ker := P.span_range_relation_eq_ker_baseChange T
/-
**Algebra.Presentation.baseChange_toGenerators** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a.Presentation`。
形式化陈述：baseChange_toGenerators : (P.baseChange T).toGenerators = P.toGenerators.b
aseChange T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma baseChange_toGenerators : (P.baseChange T).toGenerators = P.toGenerators.baseChange T := rfl

end BaseChange

section Composition

/-!
### Composition of presentations

Let `S` be an `R`-algebra with presentation `P` and `T` be an `S`-algebra with
presentation `Q`. In this section we construct a presentation of `T` as an `R`-algebra.

For the underlying generators see `Algebra.Generators.comp`. The family of relations is
indexed by `σ' ⊕ σ`.

We have two canonical maps:
`MvPolynomial ι R →ₐ[R] MvPolynomial (ι' ⊕ ι) R` induced by `Sum.inr`
and `aux : MvPolynomial (ι' ⊕ ι) R →ₐ[R] MvPolynomial ι' S` induced by
the evaluation `MvPolynomial ι R →ₐ[R] S` (see below).

Now `i : σ` is mapped to the image of `P.relation i` under the first map and
`j : σ'` is mapped to a pre-image under `aux` of `Q.relation j` (see `comp_relation_aux`
for the construction of the pre-image and `comp_relation_aux_map` for a proof that it is indeed
a pre-image).

The evaluation map factors as:
`MvPolynomial (ι' ⊕ ι) R →ₐ[R] MvPolynomial ι' S →ₐ[R] T`, where
the first map is `aux`. The goal is to compute that the kernel of this composition
is spanned by the relations indexed by `σ' ⊕ σ` (`span_range_relation_eq_ker_comp`).
One easily sees that this kernel is the pre-image under `aux` of the kernel of the evaluation
of `Q`, where the latter is by assumption spanned by the relations `Q.relation j`.

Since `aux` is surjective (`aux_surjective`), the pre-image is the sum of the ideal spanned
by the constructed pre-images of the `Q.relation j` and the kernel of `aux`. It hence
remains to show that the kernel of `aux` is spanned by the image of the `P.relation i`
under the canonical map `MvPolynomial ι R →ₐ[R] MvPolynomial (ι' ⊕ ι) R`. By
assumption this span is the kernel of the evaluation map of `P`. For this, we use the isomorphism
`MvPolynomial (ι' ⊕ ι) R ≃ₐ[R] MvPolynomial ι' (MvPolynomial ι R)` and
`MvPolynomial.ker_map`.

-/

variable {ι' σ' T : Type*} [CommRing T] [Algebra S T]
variable (Q : Presentation S T ι' σ') (P : Presentation R S ι σ)

/-- The evaluation map `MvPolynomial (ι' ⊕ ι) →ₐ[R] T` factors via this map. For more
details, see the module docstring at the beginning of the section. -/
/-
**Algebra.Presentation.aux** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Presentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The evaluation map `MvPolynomial (ι' ⊕ ι) →ₐ[R] T` factors via this map. For mor
e
details, see the module docstring at the beginning of the section.
-/
private noncomputable def aux (_Q : Presentation S T ι' σ') (P : Presentation R S ι σ) :
    MvPolynomial (ι' ⊕ ι) R →ₐ[R] MvPolynomial ι' S :=
  aeval (Sum.elim X (MvPolynomial.C ∘ P.val))

/-- A choice of pre-image of `Q.relation r` under the canonical
map `MvPolynomial (ι' ⊕ ι) R →ₐ[R] MvPolynomial ι' S` given by the evaluation of `P`. -/
/-
**Algebra.Presentation.compRelationAux** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Presen
tation`。
形式化陈述：compRelationAux (r : σ') : MvPolynomial (ι' oplus ι) R
参数：r : σ'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of pre-image of `Q.relation r` under the canonical
map `MvPolynomial (ι' ⊕ ι) R →ₐ[R] MvPolynomial ι' S` given by the evaluation of
 `P`.
-/
noncomputable def compRelationAux (r : σ') : MvPolynomial (ι' ⊕ ι) R :=
  (AddMonoidAlgebra.coeff <| Q.relation r).sum
    (fun x j ↦ (MvPolynomial.rename Sum.inr <| P.σ j) * monomial (x.mapDomain Sum.inl) 1)

@[simp]
/-
**Algebra.Presentation.aux_X** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Presentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux_X (i : ι' ⊕ ι) : (Q.aux P) (X i) = Sum.elim X (C ∘ P.val) i :=
  aeval_X (Sum.elim X (C ∘ P.val)) i

set_option backward.isDefEq.respectTransparency.types false in
/-- The pre-images constructed in `compRelationAux` are indeed pre-images under `aux`. -/
/-
**Algebra.Presentation.compRelationAux_map** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Pr
esentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pre-images constructed in `compRelationAux` are indeed pre-images under `aux
`.
-/
private lemma compRelationAux_map (r : σ') :
    (Q.aux P) (Q.compRelationAux P r) = Q.relation r := by
  simp only [aux, compRelationAux, map_finsuppSum]
  simp only [map_mul, aeval_rename, aeval_monomial, Sum.elim_comp_inr]
  conv_rhs => rw [← (Q.relation r).ofCoeff_coeff,
    ← Finsupp.sum_single (AddMonoidAlgebra.coeff <| Q.relation r)]
  rw [AddMonoidAlgebra.ofCoeff_finsuppSum]
  congr
  ext u s m
  simp only [aeval, AlgHom.coe_mk, coe_eval₂Hom, map_one, one_mul, AddMonoidAlgebra.ofCoeff_single,
    single_eq_monomial]
  rw [monomial_eq, IsScalarTower.algebraMap_eq R S, algebraMap_eq, ← eval₂_comp_left, ← aeval_def]
  simp [Finsupp.prod_mapDomain_index_inj (Sum.inl_injective)]
/-
**Algebra.Presentation.aux_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Present
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux_surjective : Function.Surjective (Q.aux P) := fun p ↦ by
  induction p using MvPolynomial.induction_on with
  | C a =>
    use rename Sum.inr <| P.σ a
    simp [aux, aeval_rename]
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | mul_X p i h =>
    obtain ⟨a, rfl⟩ := h
    exact ⟨(a * X (Sum.inl i)), by simp⟩
/-
**Algebra.Presentation.aux_image_relation** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Pre
sentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux_image_relation :
    Q.aux P '' (Set.range (Algebra.Presentation.compRelationAux Q P)) = Set.range Q.relation := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (Q.compRelationAux_map P a).symm⟩
  · rintro ⟨y, rfl⟩
    use Q.compRelationAux P y
    simp only [Set.mem_range, exists_apply_eq_apply, true_and, compRelationAux_map]
/-
**Algebra.Presentation.aux_eq_comp** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Presentati
on`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux_eq_comp : Q.aux P =
    (MvPolynomial.mapAlgHom (aeval P.val)).comp (sumAlgEquiv R ι' ι).toAlgHom := by
  ext i : 1
  cases i <;> simp
/-
**Algebra.Presentation.aux_ker** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Presentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux_ker :
    RingHom.ker (Q.aux P) = Ideal.map (rename Sum.inr) (RingHom.ker (aeval P.val)) := by
  rw [aux_eq_comp, ← AlgHom.comap_ker, MvPolynomial.ker_mapAlgHom]
  change Ideal.comap _ (Ideal.map (IsScalarTower.toAlgHom R (MvPolynomial ι R) _) _) = _
  rw [← sumAlgEquiv_comp_rename_inr, ← Ideal.map_mapₐ, Ideal.comap_map_of_bijective]
  simpa using AlgEquiv.bijective (sumAlgEquiv R ι' ι)

variable [Algebra R T] [IsScalarTower R S T]
/-
**Algebra.Presentation.aeval_comp_val_eq** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Pres
entation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aeval_comp_val_eq :
    (aeval (Q.comp P.toGenerators).val) =
      (aevalTower (IsScalarTower.toAlgHom R S T) Q.val).comp (Q.aux P) := by
  ext i
  simp only [AlgHom.coe_comp, Function.comp_apply]
  cases i <;> simp
/-
**Algebra.Presentation.span_range_relation_eq_ker_comp** 是 Mathlib 中的一个引理，位于命名空间
 `Algebra.Presentation`。
形式化陈述：span_range_relation_eq_ker_comp : Ideal.span (Set.range (Sum.elim (Algebra
.Presentation.compRelationAux Q P) fun rp => (rename Sum.inr) (P.relation rp))) 
= (Q.comp P.toGenerators).ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.Generators.ker_eq_ker_aeval_val`：ker_eq_ker_aeval_val : P.ker = 
RingHom.ker (aeval P.val)
· 使用定理 `_private.Mathlib.RingTheory.Extension.Presentation.Basic.0.Algebra.Prese
ntation.aeval_comp_val_eq`：∀ {R : Type u} {S : Type v} {ι : Type w} {σ : Type t}
 [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {ι' : Type u
_1} {σ'…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgHom.comap_ker`：comap_ker {C : Type*} [Semiring C] [Algebra R C] (f : 
B ->ₐ[R] C) (g : A ->ₐ[R] B) : (RingHom.ker f).comap g = RingHom.ker (f.comp g)
· 使用定理 `Algebra.Presentation.span_range_relation_eq_ker`：∀ {R : Type u} {S : Typ
e v} {ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2
 : Algebra R S]   (self : Algebra.Pre…
· 使用定理 `_private.Mathlib.RingTheory.Extension.Presentation.Basic.0.Algebra.Prese
ntation.aux_image_relation`：∀ {R : Type u} {S : Type v} {ι : Type w} {σ : Type t
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {ι' : Type 
u_1} {σ'…
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用引理 `Ideal.comap_map_of_surjective'`：comap_map_of_surjective' (f : F) (hf : F
unction.Surjective f) (I : Ideal R) : (I.map f).comap f = I ⊔ RingHom.ker f
· 使用定理 `_private.Mathlib.RingTheory.Extension.Presentation.Basic.0.Algebra.Prese
ntation.aux_surjective`：∀ {R : Type u} {S : Type v} {ι : Type w} {σ : Type t} [i
nst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {ι' : Type u_1}
 {σ'…
· 使用定理 `Set.Sum.elim_range`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : 
α → γ) (g : β → γ),   Set.range (Sum.elim f g) = Set.range f ∪ Set.range g
· 使用定理 `Ideal.span_union`：span_union (s t : Set α) : span (s union t) = span s ⊔
 span t
· 使用定理 `_private.Mathlib.RingTheory.Extension.Presentation.Basic.0.Algebra.Prese
ntation.aux_ker`：∀ {R : Type u} {S : Type v} {ι : Type w} {σ : Type t} [inst : C
ommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {ι' : Type u_1} {σ'…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma span_range_relation_eq_ker_comp : Ideal.span
    (Set.range (Sum.elim (Algebra.Presentation.compRelationAux Q P)
      fun rp ↦ (rename Sum.inr) (P.relation rp))) = (Q.comp P.toGenerators).ker := by
  rw [Generators.ker_eq_ker_aeval_val, Q.aeval_comp_val_eq, ← AlgHom.comap_ker]
  change _ = Ideal.comap _ (RingHom.ker (aeval Q.val))
  rw [← Q.ker_eq_ker_aeval_val, ← Q.span_range_relation_eq_ker, ← Q.aux_image_relation P,
    ← Ideal.map_span, Ideal.comap_map_of_surjective' _ (Q.aux_surjective P)]
  rw [Set.Sum.elim_range, Ideal.span_union, Q.aux_ker, ← P.ker_eq_ker_aeval_val,
    ← P.span_range_relation_eq_ker, Ideal.map_span]
  congr
  ext
  simp

/-- Given presentations of `T` over `S` and of `S` over `R`,
we may construct a presentation of `T` over `R`. -/
@[simps -isSimp relation]
/-
**Algebra.Presentation.comp** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Presentation`。
形式化陈述：comp : Presentation R T (ι' oplus ι) (σ' oplus σ) where toGenerators
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.Presentation.span_range_relation_eq_ker_comp`：span_range_relatio
n_eq_ker_comp : Ideal.span (Set.range (Sum.elim (Algebra.Presentation.compRelati
onAux Q P) fun rp => (rename Sum.inr) (P.r…

--- 原说明 ---
Given presentations of `T` over `S` and of `S` over `R`,
we may construct a presentation of `T` over `R`.
-/
noncomputable def comp : Presentation R T (ι' ⊕ ι) (σ' ⊕ σ) where
  toGenerators := Q.toGenerators.comp P.toGenerators
  relation := Sum.elim (Q.compRelationAux P)
    (fun rp ↦ MvPolynomial.rename Sum.inr <| P.relation rp)
  span_range_relation_eq_ker := Q.span_range_relation_eq_ker_comp P
/-
**Algebra.Presentation.toGenerators_comp** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Pres
entation`。
形式化陈述：toGenerators_comp : (Q.comp P).toGenerators = Q.toGenerators.comp P.toGene
rators
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toGenerators_comp : (Q.comp P).toGenerators = Q.toGenerators.comp P.toGenerators := rfl

@[simp]
/-
**Algebra.Presentation.comp_relation_inr** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Pres
entation`。
形式化陈述：comp_relation_inr (r : σ) : (Q.comp P).relation (Sum.inr r) = rename Sum.i
nr (P.relation r)
参数：r : σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_relation_inr (r : σ) :
    (Q.comp P).relation (Sum.inr r) = rename Sum.inr (P.relation r) :=
  rfl
/-
**Algebra.Presentation.comp_aeval_relation_inl** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a.Presentation`。
形式化陈述：comp_aeval_relation_inl (r : σ') : aeval (Sum.elim X (MvPolynomial.C ∘ P.v
al)) ((Q.comp P).relation (Sum.inl r)) = Q.relation r
参数：r : σ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Presentation.comp_relation`：∀ {R : Type u} {S : Type v} {ι : Typ
e w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R 
S]   {ι' : Type u_1} {σ'…
· 使用定理 `_private.Mathlib.RingTheory.Extension.Presentation.Basic.0.Algebra.Prese
ntation.compRelationAux_map`：∀ {R : Type u} {S : Type v} {ι : Type w} {σ : Type 
t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {ι' : Type
 u_1} {σ'…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_aeval_relation_inl (r : σ') :
    aeval (Sum.elim X (MvPolynomial.C ∘ P.val)) ((Q.comp P).relation (Sum.inl r)) =
      Q.relation r := by
  change (Q.aux P) _ = _
  simp [comp_relation, compRelationAux_map]

variable (g : S) [IsLocalization.Away g T] (P : Generators R S ι)

/-- The composition of a presentation `P` with a
localization away from an element has the form `R[Xᵢ, Y]/(fⱼ, (P.σ g) Y - 1)`,
if the chosen section of `P` preserves `-1` and `0`.
Note: If `S` is non-trivial, we can ensure this by only modifying `P.σ`. -/
/-
**Algebra.Presentation.relation_comp_localizationAway_inl** 是 Mathlib 中的一个引理，位于命
名空间 `Algebra.Presentation`。
形式化陈述：relation_comp_localizationAway_inl (P : Presentation R S ι σ) (h1 : P.σ (-
1) = -1) (h0 : P.σ 0 = 0) (r : Unit) : ((Presentation.localizationAway T g).comp
 P).relation (Sum.inl r) = rename Sum.inr (P.σ g) * X (Sum.inl ()) - 1
参数：P : Presentation R S ι σ；h1 : P.σ (-1) = -1；h0 : P.σ 0 = 0；r : Unit。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.Presentation.localizationAway_relation`：∀ {R : Type u} (S : Type
 v) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (r : R)   [
inst_3 : IsLocalization.Away r S] (x…
· 使用定理 `MvPolynomial.C_mul_X_eq_monomial`：C_mul_X_eq_monomial {s : σ} {a : R} : 
C a * X s = monomial (Finsupp.single s 1) a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `Finsupp.sum_single_add_single`：sum_single_add_single (f₁ f₂ : ι) (g₁ g₂ 
: A) (F : ι -> A -> B) (H : f₁ != f₂) (HF : forall f, F f 0 = 0) : sum (single f
₁ g₁ + single f₂ g₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Finsupp.mapDomain_zero`：mapDomain_zero {f : α -> β} : mapDomain f (0 : α
 ->₀ M) = (0 : β ->₀ M)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The composition of a presentation `P` with a
localization away from an element has the form `R[Xᵢ, Y]/(fⱼ, (P.σ g) Y - 1)`,
if the chosen section of `P` preserves `-1` and `0`.
Note: If `S` is non-trivial, we can ensure this by only modifying `P.σ`.
-/
lemma relation_comp_localizationAway_inl (P : Presentation R S ι σ)
    (h1 : P.σ (-1) = -1) (h0 : P.σ 0 = 0) (r : Unit) :
    ((Presentation.localizationAway T g).comp P).relation (Sum.inl r) =
      rename Sum.inr (P.σ g) * X (Sum.inl ()) - 1 := by
  simp only [Presentation.comp, Sum.elim_inl, Presentation.compRelationAux,
    Presentation.localizationAway_relation, sub_eq_add_neg, C_mul_X_eq_monomial,
    ← map_one C, ← map_neg C]
  refine (Finsupp.sum_single_add_single (Finsupp.single () 1) 0 g (-1 : S) _ ?_ ?_).trans ?_
  · simp
  · simp [h0]
  · simp [h1, ← X_pow_eq_monomial]

end Composition

/-- Given a presentation `P` and equivalences `ι' ≃ ι` and
`σ' ≃ σ`, this is the induced presentation with variables indexed
by `ι'` and relations indexed by `σ'` -/
@[simps toGenerators]
/-
**Algebra.Presentation.reindex** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Presentation`。
形式化陈述：reindex (P : Presentation R S ι σ) {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ 
σ) : Presentation R S ι' σ' where __
参数：P : Presentation R S ι σ；e : ι' ≃ ι；f : σ' ≃ σ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a presentation `P` and equivalences `ι' ≃ ι` and
`σ' ≃ σ`, this is the induced presentation with variables indexed
by `ι'` and relations indexed by `σ'`
-/
noncomputable def reindex (P : Presentation R S ι σ)
    {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ) :
    Presentation R S ι' σ' where
  __ := P.toGenerators.reindex e
  relation := rename e.symm ∘ P.relation ∘ f
  span_range_relation_eq_ker := by
    rw [Generators.ker_eq_ker_aeval_val, Generators.reindex_val, ← aeval_comp_rename,
      ← AlgHom.comap_ker, ← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker,
      Set.range_comp, Set.range_comp, Equiv.range_eq_univ, Set.image_univ,
      ← Ideal.map_span (rename ⇑e.symm)]
    have hf : Function.Bijective (MvPolynomial.rename e.symm) := (renameEquiv R e.symm).bijective
    apply Ideal.comap_injective_of_surjective _ hf.2
    simp_rw [Ideal.comap_comapₐ, rename_comp_rename, Equiv.self_comp_symm]
    simp [Ideal.comap_map_of_bijective _ hf, rename_id]

@[simp]
/-
**Algebra.Presentation.dimension_reindex** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Pres
entation`。
形式化陈述：dimension_reindex (P : Presentation R S ι σ) {ι' σ' : Type*} (e : ι' ≃ ι) 
(f : σ' ≃ σ) : (P.reindex e f).dimension = P.dimension
参数：P : Presentation R S ι σ；e : ι' ≃ ι；f : σ' ≃ σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dimension_reindex (P : Presentation R S ι σ) {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ) :
    (P.reindex e f).dimension = P.dimension := by
  simp [dimension, Nat.card_congr e, Nat.card_congr f]

section

variable {v : ι → MvPolynomial σ R}
  (s : MvPolynomial σ R ⧸ (Ideal.span <| Set.range v) → MvPolynomial σ R)
  (hs : ∀ x, Ideal.Quotient.mk _ (s x) = x)

/--
The naive presentation of a quotient `R[Xᵢ] ⧸ (vⱼ)`.
If the definitional equality of the section matters, it can be explicitly provided.
-/
@[simps! toGenerators]
noncomputable
/-
**Algebra.Presentation.naive** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Presentation`。
形式化陈述：naive {v : ι -> MvPolynomial σ R} (s : MvPolynomial σ R ⧸ (Ideal.span <| S
et.range v) -> MvPolynomial σ R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def naive {v : ι → MvPolynomial σ R}
    (s : MvPolynomial σ R ⧸ (Ideal.span <| Set.range v) → MvPolynomial σ R :=
      Function.surjInv Ideal.Quotient.mk_surjective)
    (hs : ∀ x, Ideal.Quotient.mk _ (s x) = x := by apply Function.surjInv_eq) :
    Presentation R (MvPolynomial σ R ⧸ (Ideal.span <| Set.range v)) σ ι where
  __ := Generators.naive s hs
  relation := v
  span_range_relation_eq_ker := (Generators.ker_naive s hs).symm
/-
**Algebra.Presentation.naive_relation** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Present
ation`。
形式化陈述：naive_relation : (naive s hs).relation = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma naive_relation : (naive s hs).relation = v := by rfl
/-
**Algebra.Presentation.naive_relation_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.P
resentation`。
形式化陈述：∀ {R : Type u} {ι : Type w} {σ : Type t} [inst : CommRing R] {v : ι → MvPo
lynomial σ R}   (s : MvPolynomial σ R ⧸ Ideal.span (Set.range v) → MvPolynomial 
σ R)   (hs : ∀ (x : MvPolynomial σ R ⧸ Ideal.span (Set.range v)), (Ideal.Quotien
t.mk (Ideal.span (Set.range v))) (s x) = x)   (i : ι), (Algebra.Presentation.nai
ve s hs).relation i = v i
参数：s : MvPolynomial σ R ⧸ Ideal.span (Set.range v) → MvPolynomial σ R；hs : ∀ (x 
: MvPolynomial σ R ⧸ Ideal.span (Set.range v)), (Ideal.Quotient.mk (Ideal.span (
Set.range v))) (s x) = x；i : ι；Algebra.Presentation.naive s hs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
@[simp] lemma naive_relation_apply (i : ι) : (naive s hs).relation i = v i := rfl
/-
**Algebra.Presentation.mem_ker_naive** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Presenta
tion`。
形式化陈述：mem_ker_naive (i : ι) : v i in (naive s hs).ker
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `Algebra.Presentation.relation_mem_ker`：relation_mem_ker (i) : P.relation
 i in P.ker
-/
lemma mem_ker_naive (i : ι) : v i ∈ (naive s hs).ker := relation_mem_ker _ i

end

end Construction

end Presentation

/-
**Algebra.Generators.fg_ker_of_finitePresentation** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebra.Generators`。
形式化陈述：∀ (R : Type u) (S : Type v) [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S]   [Algebra.FinitePresentation R S] {α : Type u_1} (P : Algebr
a.Generators R S α) [Finite α], P.ker.FG
参数：R : Type u；S : Type v；P : Algebra.Generators R S α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.Generators.ker_eq_ker_aeval_val`：ker_eq_ker_aeval_val : P.ker = 
RingHom.ker (aeval P.val)
· 使用定理 `Algebra.FinitePresentation.ker_fG_of_surjective`：ker_fG_of_surjective (f
 : A ->ₐ[R] B) (hf : Function.Surjective f) [FinitePresentation R A] [FinitePres
entation R B] : (RingHom.ker f.toRing…
· 使用引理 `Algebra.Generators.aeval_val_surjective`：aeval_val_surjective : Function
.Surjective (aeval (R
· 使用定理 `Algebra.FinitePresentation.mvPolynomial`：∀ (R : Type w₁) (A : Type w₂) [
inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Finit
ePresentation R A] (ι : Type …
-/
lemma Generators.fg_ker_of_finitePresentation [Algebra.FinitePresentation R S] {α : Type*}
    (P : Generators R S α) [Finite α] : P.ker.FG := by
  rw [Generators.ker_eq_ker_aeval_val]
  exact Algebra.FinitePresentation.ker_fG_of_surjective _ P.aeval_val_surjective

end Algebra

