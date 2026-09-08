/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bases

This file defines bases in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

## Main definitions

All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `Basis ι R M` is the type of `ι`-indexed `R`-bases for a module `M`,
  represented by a linear equiv `M ≃ₗ[R] ι →₀ R`.
* the basis vectors of a basis `b : Basis ι R M` are available as `b i`, where `i : ι`

* `Basis.repr` is the isomorphism sending `x : M` to its coordinates `Basis.repr x : ι →₀ R`.
  The converse, turning this isomorphism into a basis, is called `Basis.ofRepr`.
* If `ι` is finite, there is a variant of `repr` called `Basis.equivFun b : M ≃ₗ[R] ι → R`
  (saving you from having to work with `Finsupp`). The converse, turning this isomorphism into
  a basis, is called `Basis.ofEquivFun`.

* `Basis.reindex` uses an equiv to map a basis to a different indexing set.

* `Basis.map` uses a linear equiv to map a basis to a different module.

* `Basis.constr`: given `b : Basis ι R M` and `f : ι → M`, construct a linear map `g` so that
  `g (b i) = f i`.

* `Basis.coord`: `b.coord i x` is the `i`-th coordinate of a vector `x` with respect to the basis
  `b`.

## Main results

* `Basis.ext` states that two linear maps are equal if they coincide on a basis.
  Similar results are available for linear equivs (if they coincide on the basis vectors),
  elements (if their coordinates coincide) and the functions `b.repr` and `⇑b`.

## Implementation notes

We use families instead of sets because it allows us to say that two identical vectors are linearly
dependent. For bases, this is useful as well because we can easily derive ordered bases by using an
ordered index type `ι`.

## Tags

basis, bases

-/

@[expose] public section

assert_not_exists LinearMap.pi LinearIndependent Cardinal
-- TODO: assert_not_exists Submodule
-- (should be possible after splitting `Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`)

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}
variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

namespace Module

variable [Semiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (ι R M) in
/-- A `Basis ι R M` for a module `M` is the type of `ι`-indexed `R`-bases of `M`.

The basis vectors are available as `DFunLike.coe (b : Basis ι R M) : ι → M`.
To turn a linear independent family of vectors spanning `M` into a basis, use `Basis.mk`.
They are internally represented as linear equivs `M ≃ₗ[R] (ι →₀ R)`,
available as `Basis.repr`.
-/
@[wikidata Q189569]
/-
**Module.Basis** 是 Mathlib 中的一个归纳类型，位于命名空间 `Module`。
形式化陈述：Type u_1 →   (R : Type u_3) →     (M : Type u_6) →       [inst : Semiring 
R] → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → Type (max (max u_1 u_3) 
u_6)
参数：R : Type u_3；M : Type u_6；max (max u_1 u_3) u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Basis ι R M` for a module `M` is the type of `ι`-indexed `R`-bases of `M`.

The basis vectors are available as `DFunLike.coe (b : Basis ι R M) : ι → M`.
To turn a linear independent family of vectors spanning `M` into a basis, use `B
asis.mk`.
They are internally represented as linear equivs `M ≃ₗ[R] (ι →₀ R)`,
available as `Basis.repr`.
-/
structure Basis where
  /-- `Basis.ofRepr` constructs a basis given an assignment of coordinates to each vector. -/
  ofRepr ::
    /-- `repr` is the linear equivalence sending a vector `x` to its coordinates:
    the `c`s such that `x = ∑ i, c i`. -/
    repr : M ≃ₗ[R] ι →₀ R

namespace Basis

/-
**Module.Basis.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Basis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Basis ι R (ι →₀ R)) :=
  ⟨.ofRepr (LinearEquiv.refl _ _)⟩

variable (b b₁ : Basis ι R M) (i : ι) (c : R) (x : M)

section repr

/-
**Module.Basis.repr_injective** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：repr_injective : Injective (repr : Basis ι R M -> M ≃ₗ[R] ι ->₀ R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem repr_injective : Injective (repr : Basis ι R M → M ≃ₗ[R] ι →₀ R) := fun f g h => by
  cases f; cases g; congr

/-- `b i` is the `i`th basis vector. -/
/-
**Module.Basis.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `Module.Basis`。
形式化陈述：instFunLike : FunLike (Basis ι R M) ι M where coe b i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`b i` is the `i`th basis vector.
-/
instance instFunLike : FunLike (Basis ι R M) ι M where
  coe b i := b.repr.symm (Finsupp.single i 1)
  coe_injective f g h := repr_injective <| LinearEquiv.symm_bijective.injective <|
    LinearEquiv.toLinearMap_injective <| by ext; exact congr_fun h _

@[simp]
/-
**Module.Basis.coe_ofRepr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_ofRepr (e : M ≃ₗ[R] ι ->₀ R) : ⇑(ofRepr e) = fun i => e.symm (Finsupp.
single i 1)
参数：e : M ≃ₗ[R] ι ->₀ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofRepr (e : M ≃ₗ[R] ι →₀ R) : ⇑(ofRepr e) = fun i => e.symm (Finsupp.single i 1) :=
  rfl
/-
**Module.Basis.injective** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : Module.Basis ι R M) [Non
trivial R], Function.Injective ⇑b
参数：b : Module.Basis ι R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.single_left_inj`：single_left_inj (h : b != 0) : single a b = sin
gle a' b ↔ a = a'
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
protected theorem injective [Nontrivial R] : Injective b :=
  b.repr.symm.injective.comp fun _ _ => (Finsupp.single_left_inj (one_ne_zero : (1 : R) ≠ 0)).mp
/-
**Module.Basis.repr_symm_single_one** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：repr_symm_single_one : b.repr.symm (Finsupp.single i 1) = b i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem repr_symm_single_one : b.repr.symm (Finsupp.single i 1) = b i :=
  rfl
/-
**Module.Basis.repr_symm_single** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：repr_symm_single : b.repr.symm (Finsupp.single i c) = c • b i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.smul_single'`：smul_single' {_ : Semiring R} (c : R) (a : α) (b :
 R) : c • Finsupp.single a b = Finsupp.single a (c * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Module.Basis.repr_symm_single_one`：repr_symm_single_one : b.repr.symm (F
insupp.single i 1) = b i
-/
theorem repr_symm_single : b.repr.symm (Finsupp.single i c) = c • b i :=
  calc
    b.repr.symm (Finsupp.single i c) = b.repr.symm (c • Finsupp.single i (1 : R)) := by
      { rw [Finsupp.smul_single', mul_one] }
    _ = c • b i := by rw [map_smul, repr_symm_single_one]

@[simp]
/-
**Module.Basis.repr_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：repr_self : b.repr (b i) = Finsupp.single i 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem repr_self : b.repr (b i) = Finsupp.single i 1 :=
  LinearEquiv.apply_symm_apply _ _
/-
**Module.Basis.repr_self_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：repr_self_apply (j) [Decidable (i = j)] : b.repr (b i) j = if i = j then 1
 else 0
参数：j；i = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
-/
theorem repr_self_apply (j) [Decidable (i = j)] : b.repr (b i) j = if i = j then 1 else 0 := by
  rw [repr_self, Finsupp.single_apply]

@[simp]
/-
**Module.Basis.repr_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：repr_symm_apply (v) : b.repr.symm v = Finsupp.linearCombination R b v
参数：v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_single`：sum_single [AddCommMonoid M] (f : α ->₀ M) : f.sum s
ingle = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.repr_symm_single`：repr_symm_single : b.repr.symm (Finsupp.s
ingle i c) = c • b i
-/
theorem repr_symm_apply (v) : b.repr.symm v = Finsupp.linearCombination R b v :=
  calc
    b.repr.symm v = b.repr.symm (v.sum Finsupp.single) := by simp
    _ = v.sum fun i vi => b.repr.symm (Finsupp.single i vi) := map_finsuppSum ..
    _ = Finsupp.linearCombination R b v := by simp only [repr_symm_single,
                                                         Finsupp.linearCombination_apply]

@[simp]
/-
**Module.Basis.coe_repr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_repr_symm : ↑b.repr.symm = Finsupp.linearCombination R b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
-/
theorem coe_repr_symm : ↑b.repr.symm = Finsupp.linearCombination R b :=
  LinearMap.ext fun v => b.repr_symm_apply v

@[simp]
/-
**Module.Basis.repr_linearCombination** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：repr_linearCombination (v) : b.repr (Finsupp.linearCombination _ b v) = v
参数：v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.coe_repr_symm`：coe_repr_symm : ↑b.repr.symm = Finsupp.linea
rCombination R b
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem repr_linearCombination (v) : b.repr (Finsupp.linearCombination _ b v) = v := by
  rw [← b.coe_repr_symm]
  exact b.repr.apply_symm_apply v

@[simp]
/-
**Module.Basis.linearCombination_repr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：linearCombination_repr : Finsupp.linearCombination _ b (b.repr x) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.coe_repr_symm`：coe_repr_symm : ↑b.repr.symm = Finsupp.linea
rCombination R b
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem linearCombination_repr : Finsupp.linearCombination _ b (b.repr x) = x := by
  rw [← b.coe_repr_symm]
  exact b.repr.symm_apply_apply x

end repr

section Map

variable (f : M ≃ₗ[R] M')

/-- Apply the linear equivalence `f` to the basis vectors. -/
@[simps]
/-
**Module.Basis.map** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：{ι : Type u_1} →   {R : Type u_3} →     {M : Type u_6} →       {M' : Type 
u_7} →         [inst : Semiring R] →           [inst_1 : AddCommMonoid M] →     
        [inst_2 : _root_.Module R M] →               [inst_3 : AddCommMonoid M']
 →                 [inst_4 : _root_.Module R M'] → Module.Basis ι R M → (M ≃ₗ[R]
 M') → Module.Basis ι R M'
参数：M ≃ₗ[R] M'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply the linear equivalence `f` to the basis vectors.
-/
protected def map : Basis ι R M' :=
  ofRepr (f.symm.trans b.repr)

@[simp]
/-
**Module.Basis.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：map_apply (i) : b.map f i = f (b i)
参数：i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply (i) : b.map f i = f (b i) :=
  rfl
/-
**Module.Basis.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_map : (b.map f : ι -> M') = f ∘ b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map : (b.map f : ι → M') = f ∘ b :=
  rfl

end Map

section Reindex

variable (b' : Basis ι' R M')
variable (e : ι ≃ ι')

/-- `b.reindex (e : ι ≃ ι')` is a basis indexed by `ι'` -/
/-
**Module.Basis.reindex** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：reindex : Basis ι' R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`b.reindex (e : ι ≃ ι')` is a basis indexed by `ι'`
-/
def reindex : Basis ι' R M :=
  .ofRepr (b.repr.trans (Finsupp.domLCongr e))
/-
**Module.Basis.reindex_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：reindex_apply (i' : ι') : b.reindex e i' = b (e.symm i')
参数：i' : ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_trans_apply`：symm_trans_apply (c : M₃) : (e₁₂.trans e₂₃
 : M₁ ≃ₛₗ[σ₁₃] M₃).symm c = e₁₂.symm (e₂₃.symm c)
· 使用定理 `Finsupp.domLCongr_symm`：domLCongr_symm {α₁ α₂ : Type*} (f : α₁ ≃ α₂) : (
(Finsupp.domLCongr f).symm : (_ ->₀ M) ≃ₗ[R] _) = Finsupp.domLCongr f.symm
· 使用定理 `Finsupp.domLCongr_single`：domLCongr_single {α₁ : Type*} {α₂ : Type*} (e 
: α₁ ≃ α₂) (i : α₁) (m : M) : (Finsupp.domLCongr e : _ ≃ₗ[R] _) (Finsupp.single 
i m) = Finsupp…
-/
theorem reindex_apply (i' : ι') : b.reindex e i' = b (e.symm i') :=
  show (b.repr.trans (Finsupp.domLCongr e)).symm (Finsupp.single i' 1) =
    b.repr.symm (Finsupp.single (e.symm i') 1)
  by rw [LinearEquiv.symm_trans_apply, Finsupp.domLCongr_symm, Finsupp.domLCongr_single]

@[simp]
/-
**Module.Basis.coe_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Basis.reindex_apply`：reindex_apply (i' : ι') : b.reindex e i' = b
 (e.symm i')
-/
theorem coe_reindex : (b.reindex e : ι' → M) = b ∘ e.symm :=
  funext (b.reindex_apply e)
/-
**Module.Basis.repr_reindex_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：repr_reindex_apply (i' : ι') : (b.reindex e).repr x i' = b.repr x (e.symm 
i')
参数：i' : ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.domCongr_apply`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [
inst : AddCommMonoid M] (e : α ≃ β) (l : α →₀ M),   (Finsupp.domCongr e) l = Fin
supp.equivMa…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem repr_reindex_apply (i' : ι') : (b.reindex e).repr x i' = b.repr x (e.symm i') :=
  show (Finsupp.domLCongr e : _ ≃ₗ[R] _) (b.repr x) i' = _ by simp

@[simp]
/-
**Module.Basis.repr_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：repr_reindex : (b.reindex e).repr x = (b.repr x).mapDomain e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.repr_reindex_apply`：repr_reindex_apply (i' : ι') : (b.reind
ex e).repr x i' = b.repr x (e.symm i')
· 使用定理 `Finsupp.mapDomain_equiv_apply`：mapDomain_equiv_apply {f : α ≃ β} (x : α 
->₀ M) (a : β) : mapDomain f x a = x (f.symm a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem repr_reindex : (b.reindex e).repr x = (b.repr x).mapDomain e :=
  DFunLike.ext _ _ <| by simp [repr_reindex_apply]

@[simp]
/-
**Module.Basis.reindex_refl** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：reindex_refl : b.reindex (Equiv.refl ι) = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `Finsupp.domLCongr_refl`：domLCongr_refl : Finsupp.domLCongr (Equiv.refl α
) = LinearEquiv.refl R (α ->₀ M)
· 使用定理 `LinearEquiv.trans_refl`：trans_refl : e.trans (refl S M₂) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reindex_refl : b.reindex (Equiv.refl ι) = b := by
  simp [reindex]

/-- `simp` can prove this as `Basis.coe_reindex` + `EquivLike.range_comp` -/
/-
**Module.Basis.range_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：range_reindex : Set.range (b.reindex e) = Set.range b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`simp` can prove this as `Basis.coe_reindex` + `EquivLike.range_comp`
-/
theorem range_reindex : Set.range (b.reindex e) = Set.range b := by
  simp [coe_reindex, range_comp]

end Reindex

end Basis

section Fintype

open Basis

open Fintype

/-- A module over `R` with a finite basis is linearly equivalent to functions from its basis to `R`.
-/
/-
**Module.Basis.equivFun** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：{ι : Type u_1} →   {R : Type u_3} →     {M : Type u_6} →       [inst : Sem
iring R] →         [inst_1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → [
Finite ι] → Module.Basis ι R M → M ≃ₗ[R] ι → R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A module over `R` with a finite basis is linearly equivalent to functions from i
ts basis to `R`.
-/
def Basis.equivFun [Finite ι] (b : Basis ι R M) : M ≃ₗ[R] ι → R :=
  LinearEquiv.trans b.repr
    ({ Finsupp.equivFunOnFinite with
        toFun := (↑)
        map_add' := Finsupp.coe_add
        map_smul' := Finsupp.coe_smul } :
      (ι →₀ R) ≃ₗ[R] ι → R)

/-- A module over a finite ring that admits a finite basis is finite. -/
@[instance_reducible]
/-
**Module.fintypeOfFintype** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：fintypeOfFintype [Fintype ι] (b : Basis ι R M) [Fintype R] : Fintype M
参数：b : Basis ι R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
A module over a finite ring that admits a finite basis is finite.
-/
def fintypeOfFintype [Fintype ι] (b : Basis ι R M) [Fintype R] : Fintype M :=
  haveI := Classical.decEq ι
  Fintype.ofEquiv _ b.equivFun.toEquiv.symm

set_option backward.isDefEq.respectTransparency false in
/-- Given a basis `v` indexed by `ι`, the canonical linear equivalence between `ι → R` and `M` maps
a function `x : ι → R` to the linear combination `∑_i x i • v i`. -/
@[simp]
/-
**Module.Basis.equivFun_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : Fintype ι] (b : Mod
ule.Basis ι R M) (x : ι → R),   b.equivFun.symm x = ∑ i, x i • b i
参数：b : Module.Basis ι R M；x : ι → R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…

--- 原说明 ---
Given a basis `v` indexed by `ι`, the canonical linear equivalence between `ι → 
R` and `M` maps
a function `x : ι → R` to the linear combination `∑_i x i • v i`.
-/
theorem Basis.equivFun_symm_apply [Fintype ι] (b : Basis ι R M) (x : ι → R) :
    b.equivFun.symm x = ∑ i, x i • b i := by
  simp [Basis.equivFun, Finsupp.linearCombination_apply, sum_fintype, equivFunOnFinite]

@[simp]
/-
**Module.Basis.equivFun_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : Finite ι] (b : Modu
le.Basis ι R M) (u : M), b.equivFun u = ⇑(b.repr u)
参数：b : Module.Basis ι R M；u : M；b.repr u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Basis.equivFun_apply [Finite ι] (b : Basis ι R M) (u : M) : b.equivFun u = b.repr u :=
  rfl

@[simp]
/-
**Module.Basis.map_equivFun** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} {M' : Type u_7} [inst : Sem
iring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : Add
CommMonoid M'] [inst_4 : _root_.Module R M'] [inst_5 : Finite ι]   (b : Module.B
asis ι R M) (f : M ≃ₗ[R] M'), (b.map f).equivFun = f.symm ≪≫ₗ b.equivFun
参数：b : Module.Basis ι R M；f : M ≃ₗ[R] M'；b.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Basis.map_equivFun [Finite ι] (b : Basis ι R M) (f : M ≃ₗ[R] M') :
    (b.map f).equivFun = f.symm.trans b.equivFun :=
  rfl
/-
**Module.Basis.sum_equivFun** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : Fintype ι] (b : Mod
ule.Basis ι R M) (u : M), ∑ i, b.equivFun u i • b i = u
参数：b : Module.Basis ι R M；u : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem Basis.sum_equivFun [Fintype ι] (b : Basis ι R M) (u : M) :
    ∑ i, b.equivFun u i • b i = u := by
  rw [← b.equivFun_symm_apply, b.equivFun.symm_apply_apply]

@[simp]
/-
**Module.Basis.sum_repr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : Fintype ι] (b : Mod
ule.Basis ι R M) (u : M), ∑ i, (b.repr u) i • b i = u
参数：b : Module.Basis ι R M；u : M；b.repr u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.sum_equivFun`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6
} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : Finty…
-/
theorem Basis.sum_repr [Fintype ι] (b : Basis ι R M) (u : M) : ∑ i, b.repr u i • b i = u :=
  b.sum_equivFun u

@[simp]
/-
**Module.Basis.equivFun_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : Finite ι] [inst_4 :
 DecidableEq ι] (b : Module.Basis ι R M) (i j : ι),   b.equivFun (b i) j = if i 
= j then 1 else 0
参数：b : Module.Basis ι R M；i j : ι；b i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.equivFun_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u
_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] [inst_3 : Finit…
· 使用定理 `Module.Basis.repr_self_apply`：repr_self_apply (j) [Decidable (i = j)] : 
b.repr (b i) j = if i = j then 1 else 0
-/
theorem Basis.equivFun_self [Finite ι] [DecidableEq ι] (b : Basis ι R M) (i j : ι) :
    b.equivFun (b i) j = if i = j then 1 else 0 := by rw [b.equivFun_apply, b.repr_self_apply]
/-
**Module.Basis.repr_sum_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : Fintype ι] (b : Mod
ule.Basis ι R M) (c : ι → R), ⇑(b.repr (∑ i, c i • b i)) = c
参数：b : Module.Basis ι R M；c : ι → R；b.repr (∑ i, c i • b i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Basis.repr_sum_self [Fintype ι] (b : Basis ι R M) (c : ι → R) :
    b.repr (∑ i, c i • b i) = c := by
  simp_rw [← b.equivFun_symm_apply, ← b.equivFun_apply, b.equivFun.apply_symm_apply]

/-- Define a basis by mapping each vector `x : M` to its coordinates `e x : ι → R`,
as long as `ι` is finite. -/
/-
**Module.Basis.ofEquivFun** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：{ι : Type u_1} →   {R : Type u_3} →     {M : Type u_6} →       [inst : Sem
iring R] →         [inst_1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → [
Finite ι] → (M ≃ₗ[R] ι → R) → Module.Basis ι R M
参数：M ≃ₗ[R] ι → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a basis by mapping each vector `x : M` to its coordinates `e x : ι → R`,
as long as `ι` is finite.
-/
def Basis.ofEquivFun [Finite ι] (e : M ≃ₗ[R] ι → R) : Basis ι R M :=
  .ofRepr <| e.trans <| LinearEquiv.symm <| Finsupp.linearEquivFunOnFinite R R ι

@[simp]
/-
**Module.Basis.ofEquivFun_repr_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : Finite ι] (e : M ≃ₗ
[R] ι → R) (x : M) (i : ι),   ((Module.Basis.ofEquivFun e).repr x) i = e x i
参数：e : M ≃ₗ[R] ι → R；x : M；i : ι；(Module.Basis.ofEquivFun e).repr x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Basis.ofEquivFun_repr_apply [Finite ι] (e : M ≃ₗ[R] ι → R) (x : M) (i : ι) :
    (Basis.ofEquivFun e).repr x i = e x i :=
  rfl

@[simp]
/-
**Module.Basis.coe_ofEquivFun** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : Finite ι] [inst_4 :
 DecidableEq ι] (e : M ≃ₗ[R] ι → R),   ⇑(Module.Basis.ofEquivFun e) = fun i => e
.symm (Pi.single i 1)
参数：e : M ≃ₗ[R] ι → R；Module.Basis.ofEquivFun e；Pi.single i 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.linearEquivFunOnFinite_single`：linearEquivFunOnFinite_single [De
cidableEq α] (x : α) (m : M) : (linearEquivFunOnFinite R M α) (single x m) = Pi.
single x m
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Basis.coe_ofEquivFun [Finite ι] [DecidableEq ι] (e : M ≃ₗ[R] ι → R) :
    (Basis.ofEquivFun e : ι → M) = fun i => e.symm (Pi.single i 1) :=
  funext fun i =>
    e.injective <|
      funext fun j => by
        simp [Basis.ofEquivFun, ← Finsupp.single_eq_pi_single]

@[simp]
/-
**Module.Basis.ofEquivFun_equivFun** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : Finite ι] (v : Modu
le.Basis ι R M), Module.Basis.ofEquivFun v.equivFun = v
参数：v : Module.Basis ι R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.repr_injective`：repr_injective : Injective (repr : Basis ι 
R M -> M ≃ₗ[R] ι ->₀ R)
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem Basis.ofEquivFun_equivFun [Finite ι] (v : Basis ι R M) :
    Basis.ofEquivFun v.equivFun = v :=
  Basis.repr_injective <| by ext; rfl

@[simp]
/-
**Module.Basis.equivFun_ofEquivFun** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : Finite ι] (e : M ≃ₗ
[R] ι → R), (Module.Basis.ofEquivFun e).equivFun = e
参数：e : M ≃ₗ[R] ι → R；Module.Basis.ofEquivFun e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Basis.equivFun_ofEquivFun [Finite ι] (e : M ≃ₗ[R] ι → R) :
    (Basis.ofEquivFun e).equivFun = e := by
  ext j
  simp_rw [Basis.equivFun_apply, Basis.ofEquivFun_repr_apply]

end Fintype

variable {ι R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

namespace Basis

variable (b : Basis ι R M)

section Ext

variable {R₁ : Type*} [Semiring R₁] {σ : R →+* R₁} {σ' : R₁ →+* R}
variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
variable {M₁ : Type*} [AddCommMonoid M₁] [Module R₁ M₁]

/-- Two linear maps are equal if they are equal on basis vectors. -/
/-
**Module.Basis.ext** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f₂ (b i)) : f₁ = f₂
参数：h : forall i, f₁ (b i) = f₂ (b i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Two linear maps are equal if they are equal on basis vectors.
-/
theorem ext {f₁ f₂ : M →ₛₗ[σ] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ := by
  ext x
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [map_sum, map_smulₛₗ, h]

/-- Two linear equivs are equal if they are equal on basis vectors. -/
/-
**Module.Basis.ext'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：ext' {f₁ f₂ : M ≃ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f₂ (b i)) : f₁ = f₂
参数：h : forall i, f₁ (b i) = f₂ (b i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Two linear equivs are equal if they are equal on basis vectors.
-/
theorem ext' {f₁ f₂ : M ≃ₛₗ[σ] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ := by
  ext x
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [map_sum, map_smulₛₗ, h]

/-- Two elements are equal iff their coordinates are equal. -/
/-
**Module.Basis.ext_elem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：ext_elem_iff {x y : M} : x = y ↔ forall i, b.repr x i = b.repr y i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Two elements are equal iff their coordinates are equal.
-/
theorem ext_elem_iff {x y : M} : x = y ↔ ∀ i, b.repr x i = b.repr y i := by
  simp only [← DFunLike.ext_iff, EmbeddingLike.apply_eq_iff_eq]

alias ⟨_, ext_elem⟩ := ext_elem_iff
/-
**Module.Basis.repr_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：repr_eq_iff {b : Basis ι R M} {f : M ->ₗ[R] ι ->₀ R} : ↑b.repr = f ↔ foral
l i, f (b i) = Finsupp.single i 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem repr_eq_iff {b : Basis ι R M} {f : M →ₗ[R] ι →₀ R} :
    ↑b.repr = f ↔ ∀ i, f (b i) = Finsupp.single i 1 :=
  ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext fun i => (b.repr_self i).trans (h i).symm⟩
/-
**Module.Basis.repr_eq_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：repr_eq_iff' {b : Basis ι R M} {f : M ≃ₗ[R] ι ->₀ R} : b.repr = f ↔ forall
 i, f (b i) = Finsupp.single i 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Module.Basis.ext'`：ext' {f₁ f₂ : M ≃ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = 
f₂ (b i)) : f₁ = f₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem repr_eq_iff' {b : Basis ι R M} {f : M ≃ₗ[R] ι →₀ R} :
    b.repr = f ↔ ∀ i, f (b i) = Finsupp.single i 1 :=
  ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext' fun i => (b.repr_self i).trans (h i).symm⟩
/-
**Module.Basis.apply_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：apply_eq_iff {b : Basis ι R M} {x : M} {i : ι} : b i = x ↔ b.repr x = Fins
upp.single i 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem apply_eq_iff {b : Basis ι R M} {x : M} {i : ι} : b i = x ↔ b.repr x = Finsupp.single i 1 :=
  ⟨fun h => h ▸ b.repr_self i, fun h => b.repr.injective ((b.repr_self i).trans h.symm)⟩

/-- An unbundled version of `repr_eq_iff` -/
/-
**Module.Basis.repr_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：repr_apply_eq (f : M -> ι -> R) (hadd : forall x y, f (x + y) = f x + f y)
 (hsmul : forall (c : R) (x : M), f (c • x) = c • f x) (f_eq : forall i, f (b i)
 = Finsupp.single i 1) (x : M) (i : ι) : b.repr x i = f x i
参数：f : M -> ι -> R；hadd : forall x y, f (x + y) = f x + f y；hsmul : forall (c : 
R) (x : M), f (c • x) = c • f x；f_eq : forall i, f (b i) = Finsupp.single i 1；x 
: M；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
An unbundled version of `repr_eq_iff`
-/
theorem repr_apply_eq (f : M → ι → R) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (c : R) (x : M), f (c • x) = c • f x) (f_eq : ∀ i, f (b i) = Finsupp.single i 1)
    (x : M) (i : ι) : b.repr x i = f x i := by
  let f_i : M →ₗ[R] R :=
    { toFun x := f x i
      map_add' _ _ := by rw [hadd, Pi.add_apply]
      map_smul' _ _ := by simp [hsmul, Pi.smul_apply] }
  have : Finsupp.lapply i ∘ₗ ↑b.repr = f_i := by
    refine b.ext fun j => ?_
    change b.repr (b j) i = f (b j) i
    rw [b.repr_self, f_eq]
  calc
    b.repr x i = f_i x := by
      { rw [← this]
        rfl }
    _ = f x i := rfl

/-- Two bases are equal if they assign the same coordinates. -/
/-
**Module.Basis.eq_ofRepr_eq_repr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：eq_ofRepr_eq_repr {b₁ b₂ : Basis ι R M} (h : forall x i, b₁.repr x i = b₂.
repr x i) : b₁ = b₂
参数：h : forall x i, b₁.repr x i = b₂.repr x i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.repr_injective`：repr_injective : Injective (repr : Basis ι 
R M -> M ≃ₗ[R] ι ->₀ R)
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g

--- 原说明 ---
Two bases are equal if they assign the same coordinates.
-/
theorem eq_ofRepr_eq_repr {b₁ b₂ : Basis ι R M} (h : ∀ x i, b₁.repr x i = b₂.repr x i) : b₁ = b₂ :=
  repr_injective <| by ext; apply h

/-- Two bases are equal if their basis vectors are the same. -/
@[ext]
/-
**Module.Basis.eq_of_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (forall i, b₁ i = b₂ i) -> b₁ = b₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g

--- 原说明 ---
Two bases are equal if their basis vectors are the same.
-/
theorem eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (∀ i, b₁ i = b₂ i) → b₁ = b₂ :=
  DFunLike.ext _ _

end Ext

section MapCoeffs

variable {R' : Type*} [Semiring R'] [Module R' M] (f : R ≃+* R')

attribute [local instance] SMul.comp.isScalarTower

set_option backward.isDefEq.respectTransparency false in
/-- If `R` and `R'` are isomorphic rings that act identically on a module `M`,
then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module.

See also `Basis.algebraMapCoeffs` for the case where `f` is equal to `algebraMap`.
-/
@[simps +simpRhs]
/-
**Module.Basis.mapCoeffs** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：mapCoeffs (h : forall (c) (x : M), f c • x = c • x) : Basis ι R' M
参数：h : forall (c) (x : M), f c • x = c • x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` and `R'` are isomorphic rings that act identically on a module `M`,
then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module.

See also `Basis.algebraMapCoeffs` for the case where `f` is equal to `algebraMap
`.
-/
def mapCoeffs (h : ∀ (c) (x : M), f c • x = c • x) : Basis ι R' M := by
  letI : Module R' R := Module.compHom R (↑f.symm : R' →+* R)
  haveI : IsScalarTower R' R M :=
    { smul_assoc := fun x y z => by
        change (f.symm x * y) • z = x • (y • z)
        rw [mul_smul, ← h, f.apply_symm_apply] }
  exact ofRepr <| (b.repr.restrictScalars R').trans <|
    Finsupp.mapRange.linearEquiv (Module.compHom.toLinearEquiv f.symm).symm

variable (h : ∀ (c) (x : M), f c • x = c • x)
/-
**Module.Basis.mapCoeffs_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：mapCoeffs_apply (i : ι) : b.mapCoeffs f h i = b i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Basis.apply_eq_iff`：apply_eq_iff {b : Basis ι R M} {x : M} {i : ι
} : b i = x ↔ b.repr x = Finsupp.single i 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.mapCoeffs_repr`：∀ {ι : Type u_10} {R : Type u_11} {M : Type
 u_12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.…
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
· 使用定理 `LinearEquiv.restrictScalars_apply`：∀ (R : Type u_1) {S : Type u_4} {M : 
Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : 
AddCommMonoid M] [inst_…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.mapRange.linearEquiv_apply`：∀ {α : Type u_1} {M : Type u_2} {N :
 Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring
 R₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Module.compHom.toLinearEquiv_symm_apply`：∀ {R : Type u_9} {S : Type u_10
} [inst : Semiring R] [inst_1 : Semiring S] (g : R ≃+* S) (a : S),   (Module.com
pHom.toLinearEquiv g).symm a …
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
theorem mapCoeffs_apply (i : ι) : b.mapCoeffs f h i = b i :=
  apply_eq_iff.mpr <| by simp

@[simp]
/-
**Module.Basis.coe_mapCoeffs** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_mapCoeffs : (b.mapCoeffs f h : ι -> M) = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.mapCoeffs_apply`：mapCoeffs_apply (i : ι) : b.mapCoeffs f h 
i = b i
-/
theorem coe_mapCoeffs : (b.mapCoeffs f h : ι → M) = b :=
  funext <| b.mapCoeffs_apply f h

end MapCoeffs

section ReindexRange

/-- `b.reindexRange` is a basis indexed by `range b`, the basis vectors themselves. -/
/-
**Module.Basis.reindexRange** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：reindexRange : Basis (range b) R M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.injective`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [
inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b 
: Module.Bas…

--- 原说明 ---
`b.reindexRange` is a basis indexed by `range b`, the basis vectors themselves.
-/
def reindexRange : Basis (range b) R M :=
  haveI := Classical.dec (Nontrivial R)
  if h : Nontrivial R then
    b.reindex (Equiv.ofInjective b (Basis.injective b))
  else
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    .ofRepr (Module.subsingletonEquiv R M (range b))
/-
**Module.Basis.reindexRange_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：reindexRange_self (i : ι) (h
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Module.Basis.injective`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [
inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b 
: Module.Bas…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Module.Basis.reindex_apply`：reindex_apply (i' : ι') : b.reindex e i' = b
 (e.symm i')
· 使用定理 `Equiv.ofInjective_symm_apply`：ofInjective_symm_apply {α β} {f : α -> β} 
(hf : Injective f) (a : α) : (ofInjective f hf).symm ⟨f a, ⟨a, rfl⟩⟩ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reindexRange_self (i : ι) (h := Set.mem_range_self i) : b.reindexRange ⟨b i, h⟩ = b i := by
  cases subsingleton_or_nontrivial R
  · let := Module.subsingleton R M
    simp [reindexRange, eq_iff_true_of_subsingleton]
  · simp [*, reindexRange, reindex_apply]
/-
**Module.Basis.reindexRange_repr_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：reindexRange_repr_self (i : ι) : b.reindexRange.repr (b i) = Finsupp.singl
e ⟨b i, mem_range_self i⟩ 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.reindexRange_self`：reindexRange_self (i : ι) (h
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
-/
theorem reindexRange_repr_self (i : ι) :
    b.reindexRange.repr (b i) = Finsupp.single ⟨b i, mem_range_self i⟩ 1 :=
  calc
    b.reindexRange.repr (b i) = b.reindexRange.repr (b.reindexRange ⟨b i, mem_range_self i⟩) :=
      congr_arg _ (b.reindexRange_self _ _).symm
    _ = Finsupp.single ⟨b i, mem_range_self i⟩ 1 := b.reindexRange.repr_self _

@[simp]
/-
**Module.Basis.reindexRange_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：reindexRange_apply (x : range b) : b.reindexRange x = x
参数：x : range b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.reindexRange_self`：reindexRange_self (i : ι) (h
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem reindexRange_apply (x : range b) : b.reindexRange x = x := by
  rcases x with ⟨bi, ⟨i, rfl⟩⟩
  exact b.reindexRange_self i

set_option backward.isDefEq.respectTransparency false in
/-
**Module.Basis.reindexRange_repr'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：reindexRange_repr' (x : M) {bi : M} {i : ι} (h : b i = bi) : b.reindexRang
e.repr x ⟨bi, ⟨i, h⟩⟩ = b.repr x i
参数：x : M；h : b i = bi。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.repr_apply_eq`：repr_apply_eq (f : M -> ι -> R) (hadd : fora
ll x y, f (x + y) = f x + f y) (hsmul : forall (c : R) (x : M), f (c • x) = c • 
f x) (f_eq : for…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Module.Basis.reindexRange_repr_self`：reindexRange_repr_self (i : ι) : b.
reindexRange.repr (b i) = Finsupp.single ⟨b i, mem_range_self i⟩ 1
· 使用定理 `Finsupp.single_apply_left`：single_apply_left {f : α -> β} (hf : Function
.Injective f) (x z : α) (y : M) : single (f x) y (f z) = single x y z
· 使用定理 `Module.Basis.injective`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [
inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b 
: Module.Bas…
· 使用定理 `Subtype.mk.inj`：∀ {α : Sort u} {p : α → Prop} {val : α} {property : p va
l} {val_1 : α} {property_1 : p val_1},   ⟨val, property⟩ = ⟨val_1, property_1⟩ →
 val…
-/
theorem reindexRange_repr' (x : M) {bi : M} {i : ι} (h : b i = bi) :
    b.reindexRange.repr x ⟨bi, ⟨i, h⟩⟩ = b.repr x i := by
  nontriviality
  subst h
  apply (b.repr_apply_eq (fun x i => b.reindexRange.repr x ⟨b i, _⟩) _ _ _ x i).symm
  · intro x y
    ext i
    simp only [Pi.add_apply, map_add, Finsupp.coe_add]
  · intro c x
    ext i
    simp
  · intro i
    ext j
    simp only [reindexRange_repr_self]
    apply Finsupp.single_apply_left (f := fun i => (⟨b i, _⟩ : Set.range b))
    exact fun i j h => b.injective (Subtype.mk.inj h)

@[simp]
/-
**Module.Basis.reindexRange_repr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：reindexRange_repr (x : M) (i : ι) (h
参数：x : M；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.reindexRange_repr'`：reindexRange_repr' (x : M) {bi : M} {i 
: ι} (h : b i = bi) : b.reindexRange.repr x ⟨bi, ⟨i, h⟩⟩ = b.repr x i
-/
theorem reindexRange_repr (x : M) (i : ι) (h := Set.mem_range_self i) :
    b.reindexRange.repr x ⟨b i, h⟩ = b.repr x i :=
  b.reindexRange_repr' _ rfl

section Fintype

variable [Fintype ι] [DecidableEq M]

/-- `b.reindexFinsetRange` is a basis indexed by `Finset.univ.image b`,
the finite set of basis vectors themselves. -/
/-
**Module.Basis.reindexFinsetRange** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：reindexFinsetRange : Basis (Finset.univ.image b) R M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`b.reindexFinsetRange` is a basis indexed by `Finset.univ.image b`,
the finite set of basis vectors themselves.
-/
def reindexFinsetRange : Basis (Finset.univ.image b) R M :=
  b.reindexRange.reindex ((Equiv.refl M).subtypeEquiv (by simp))
/-
**Module.Basis.reindexFinsetRange_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：reindexFinsetRange_self (i : ι) (h
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.reindexFinsetRange.eq_1`：∀ {ι : Type u_10} {R : Type u_11} 
{M : Type u_12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root
_.Module R M] (b : Module.…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Basis.reindex_apply`：reindex_apply (i' : ι') : b.reindex e i' = b
 (e.symm i')
· 使用定理 `Module.Basis.reindexRange_apply`：reindexRange_apply (x : range b) : b.re
indexRange x = x
-/
theorem reindexFinsetRange_self (i : ι) (h := Finset.mem_image_of_mem b (Finset.mem_univ i)) :
    b.reindexFinsetRange ⟨b i, h⟩ = b i := by
  rw [reindexFinsetRange, reindex_apply, reindexRange_apply]
  rfl

@[simp]
/-
**Module.Basis.reindexFinsetRange_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`
。
形式化陈述：reindexFinsetRange_apply (x : Finset.univ.image b) : b.reindexFinsetRange 
x = x
参数：x : Finset.univ.image b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Module.Basis.reindexFinsetRange_self`：reindexFinsetRange_self (i : ι) (h
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem reindexFinsetRange_apply (x : Finset.univ.image b) : b.reindexFinsetRange x = x := by
  rcases x with ⟨bi, hbi⟩
  rcases Finset.mem_image.mp hbi with ⟨i, -, rfl⟩
  exact b.reindexFinsetRange_self i
/-
**Module.Basis.reindexFinsetRange_repr_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Ba
sis`。
形式化陈述：reindexFinsetRange_repr_self (i : ι) : b.reindexFinsetRange.repr (b i) = F
insupp.single ⟨b i, Finset.mem_image_of_mem b (Finset.mem_univ i)⟩ 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.reindexFinsetRange.eq_1`：∀ {ι : Type u_10} {R : Type u_11} 
{M : Type u_12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root
_.Module R M] (b : Module.…
· 使用定理 `Module.Basis.repr_reindex`：repr_reindex : (b.reindex e).repr x = (b.repr
 x).mapDomain e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finsupp.mapDomain_equiv_apply`：mapDomain_equiv_apply {f : α ≃ β} (x : α 
->₀ M) (a : β) : mapDomain f x a = x (f.symm a)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Module.Basis.reindexRange_repr_self`：reindexRange_repr_self (i : ι) : b.
reindexRange.repr (b i) = Finsupp.single ⟨b i, mem_range_self i⟩ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.subtypeEquiv_apply`：∀ {α : Sort u_1} {β : Sort u_4} {p : α → Prop}
 {q : β → Prop} (e : α ≃ β) (h : ∀ (a : α), p a ↔ q (e a))   (a : { a // p a }),
 (e.subtypeEqu…
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reindexFinsetRange_repr_self (i : ι) :
    b.reindexFinsetRange.repr (b i) =
      Finsupp.single ⟨b i, Finset.mem_image_of_mem b (Finset.mem_univ i)⟩ 1 := by
  ext ⟨bi, hbi⟩
  rw [reindexFinsetRange, repr_reindex, Finsupp.mapDomain_equiv_apply, reindexRange_repr_self]
  simp [Finsupp.single_apply]

@[simp]
/-
**Module.Basis.reindexFinsetRange_repr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：reindexFinsetRange_repr (x : M) (i : ι) (h
参数：x : M；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Module.Basis.repr_reindex`：repr_reindex : (b.reindex e).repr x = (b.repr
 x).mapDomain e
· 使用定理 `Finsupp.mapDomain_equiv_apply`：mapDomain_equiv_apply {f : α ≃ β} (x : α 
->₀ M) (a : β) : mapDomain f x a = x (f.symm a)
· 使用定理 `Equiv.subtypeEquiv_apply`：∀ {α : Sort u_1} {β : Sort u_4} {p : α → Prop}
 {q : β → Prop} (e : α ≃ β) (h : ∀ (a : α), p a ↔ q (e a))   (a : { a // p a }),
 (e.subtypeEqu…
· 使用定理 `Module.Basis.reindexRange_repr`：reindexRange_repr (x : M) (i : ι) (h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reindexFinsetRange_repr (x : M) (i : ι)
    (h := Finset.mem_image_of_mem b (Finset.mem_univ i)) :
    b.reindexFinsetRange.repr x ⟨b i, h⟩ = b.repr x i := by simp [reindexFinsetRange]

end Fintype

end ReindexRange

variable [Module R M']

section Constr

variable (S : Type*) [Semiring S] [Module S M']
variable [SMulCommClass R S M']

/-- Construct a linear map given the value at the basis, called `Basis.constr b S f` where `b` is
a basis, `f` is the value of the linear map over the elements of the basis, and `S` is an
extra semiring (typically `S = R` or `S = ℕ`).

This definition is parameterized over an extra `Semiring S`,
such that `SMulCommClass R S M'` holds.
If `R` is commutative, you can set `S := R`; if `R` is not commutative,
you can recover an `AddEquiv` by setting `S := ℕ`.
See library note [bundled maps over different rings].
-/
/-
**Module.Basis.constr** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：constr : (ι -> M') ≃ₗ[S] M ->ₗ[R] M' where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a linear map given the value at the basis, called `Basis.constr b S f`
 where `b` is
a basis, `f` is the value of the linear map over the elements of the basis, and 
`S` is an
extra semiring (typically `S = R` or `S = ℕ`).

This definition is parameterized over an extra `Semiring S`,
such that `SMulCommClass R S M'` holds.
If `R` is commutative, you can set `S := R`; if `R` is not commutative,
you can recover an `AddEquiv` by setting `S := ℕ`.
See library note [bundled maps over different rings].
-/
def constr : (ι → M') ≃ₗ[S] M →ₗ[R] M' where
  toFun f := (Finsupp.linearCombination R id).comp <| Finsupp.lmapDomain R R f ∘ₗ ↑b.repr
  invFun f i := f (b i)
  left_inv f := by
    ext
    simp
  right_inv f := by
    refine b.ext fun i => ?_
    simp
  map_add' f g := by
    refine b.ext fun i => ?_
    simp
  map_smul' c f := by
    refine b.ext fun i => ?_
    simp
/-
**Module.Basis.constr_def** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：constr_def (f : ι -> M') : constr (M'
参数：f : ι -> M'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constr_def (f : ι → M') :
    constr (M' := M') b S f = linearCombination R id ∘ₗ Finsupp.lmapDomain R R f ∘ₗ ↑b.repr :=
  rfl
/-
**Module.Basis.constr_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：constr_apply (f : ι -> M') (x : M) : constr (M'
参数：f : ι -> M'；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_mapDomain_index`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f : α 
→ β} {s : α →₀ M}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
-/
theorem constr_apply (f : ι → M') (x : M) :
    constr (M' := M') b S f x = (b.repr x).sum fun b a => a • f b := by
  simp only [constr_def, LinearMap.comp_apply, lmapDomain_apply, linearCombination_apply]
  rw [Finsupp.sum_mapDomain_index] <;> simp [add_smul]
/-
**Module.Basis.constr_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {M' : Type u_7} [inst : AddCommMonoid M'] {ι : Type u_10} {R : Type u_11
} {M : Type u_12} [inst_1 : Semiring R]   [inst_2 : AddCommMonoid M] [inst_3 : _
root_.Module R M] (b : Module.Basis ι R M) [inst_4 : _root_.Module R M']   (S : 
Type u_13) [inst_5 : Semiring S] [inst_6 : _root_.Module S M'] [inst_7 : SMulCom
mClass R S M'] (f : M →ₗ[R] M')   (i : ι), (b.constr S).symm f i = f (b i)
参数：b : Module.Basis ι R M；S : Type u_13；f : M →ₗ[R] M'；i : ι；b.constr S；b i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem constr_symm_apply (f : M →ₗ[R] M') (i) :
    (b.constr S).symm f i = f (b i) := by
  rfl

@[simp]
/-
**Module.Basis.constr_basis** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：constr_basis (f : ι -> M') (i : ι) : (constr (M'
参数：f : ι -> M'；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.constr_apply`：constr_apply (f : ι -> M') (x : M) : constr (
M'
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem constr_basis (f : ι → M') (i : ι) : (constr (M' := M') b S f : M → M') (b i) = f i := by
  simp [Basis.constr_apply, b.repr_self]
/-
**Module.Basis.constr_eq** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：constr_eq {g : ι -> M'} {f : M ->ₗ[R] M'} (h : forall i, g i = f (b i)) : 
constr (M'
参数：h : forall i, g i = f (b i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.constr_basis`：constr_basis (f : ι -> M') (i : ι) : (constr 
(M'
-/
theorem constr_eq {g : ι → M'} {f : M →ₗ[R] M'} (h : ∀ i, g i = f (b i)) :
    constr (M' := M') b S g = f :=
  b.ext fun i => (b.constr_basis S g i).trans (h i)
/-
**Module.Basis.constr_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：constr_self (f : M ->ₗ[R] M') : (constr (M'
参数：f : M ->ₗ[R] M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.constr_eq`：constr_eq {g : ι -> M'} {f : M ->ₗ[R] M'} (h : f
orall i, g i = f (b i)) : constr (M'
-/
theorem constr_self (f : M →ₗ[R] M') : (constr (M' := M') b S fun i => f (b i)) = f :=
  b.constr_eq S fun _ => rfl
/-
**Module.Basis.constr_range** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：constr_range {f : ι -> M'} : LinearMap.range (constr (M'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.constr_def`：constr_def (f : ι -> M') : constr (M'
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.supported_univ`：supported_univ : supported M R (Set.univ : Set α
) = ⊤
· 使用定理 `Finsupp.lmapDomain_supported`：lmapDomain_supported (f : α -> α') (s : Se
t α) : (supported M R s).map (lmapDomain M R f) = supported M R (f '' s)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Finsupp.span_image_eq_map_linearCombination`：span_image_eq_map_linearCom
bination (s : Set α) : span R (v '' s) = Submodule.map (linearCombination R v) (
supported R R s)
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem constr_range {f : ι → M'} :
    LinearMap.range (constr (M' := M') b S f) = span R (range f) := by
  rw [b.constr_def S f, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, ←
    Finsupp.supported_univ, Finsupp.lmapDomain_supported, ← Set.image_univ, ←
    Finsupp.span_image_eq_map_linearCombination, Set.image_id]

@[simp]
/-
**Module.Basis.constr_comp** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：constr_comp (f : M' ->ₗ[R] M') (v : ι -> M') : constr (M'
参数：f : M' ->ₗ[R] M'；v : ι -> M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.constr_basis`：constr_basis (f : ι -> M') (i : ι) : (constr 
(M'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constr_comp (f : M' →ₗ[R] M') (v : ι → M') :
    constr (M' := M') b S (f ∘ v) = f.comp (constr (M' := M') b S v) :=
  b.ext fun i => by simp only [Basis.constr_basis, LinearMap.comp_apply, Function.comp]

variable (S : Type*) [Semiring S] [Module S M']
variable [SMulCommClass R S M']

@[simp]
/-
**Module.Basis.constr_apply_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：constr_apply_fintype [Fintype ι] (b : Basis ι R M) (f : ι -> M') (x : M) :
 (constr (M'
参数：b : Basis ι R M；f : ι -> M'；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.constr_apply`：constr_apply (f : ι -> M') (x : M) : constr (
M'
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem constr_apply_fintype [Fintype ι] (b : Basis ι R M) (f : ι → M') (x : M) :
    (constr (M' := M') b S f : M → M') x = ∑ i, b.equivFun x i • f i := by
  simp [b.constr_apply, b.equivFun_apply, Finsupp.sum_fintype]

end Constr

section Equiv

variable (i : ι)
variable {M'' : Type*} (b' : Basis ι' R M') (e : ι ≃ ι')
variable [AddCommMonoid M''] [Module R M'']

/-- If `b` is a basis for `M` and `b'` a basis for `M'`, and the index types are equivalent,
`b.equiv b' e` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `b' (e i)`. -/
/-
**Module.Basis.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：{ι' : Type u_2} →   {M' : Type u_7} →     [inst : AddCommMonoid M'] →     
  {ι : Type u_10} →         {R : Type u_11} →           {M : Type u_12} →       
      [inst_1 : Semiring R] →               [inst_2 : AddCommMonoid M] →        
         [inst_3 : _root_.Module R M] →                   Module.Basis ι R M → [
inst_4 : _root_.Module R M'] → Module.Basis ι' R M' → ι ≃ ι' → M ≃ₗ[R] M'
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `b` is a basis for `M` and `b'` a basis for `M'`, and the index types are equ
ivalent,
`b.equiv b' e` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `b' (e i)`
.
-/
protected def equiv : M ≃ₗ[R] M' :=
  b.repr.trans (b'.reindex e.symm).repr.symm

@[simp]
/-
**Module.Basis.equiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：equiv_apply : b.equiv b' e (b i) = b' (e i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equiv_apply : b.equiv b' e (b i) = b' (e i) := by simp [Basis.equiv]

@[simp]
/-
**Module.Basis.equiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：equiv_refl : b.equiv b (Equiv.refl ι) = LinearEquiv.refl R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext'`：ext' {f₁ f₂ : M ≃ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = 
f₂ (b i)) : f₁ = f₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.equiv_apply`：equiv_apply : b.equiv b' e (b i) = b' (e i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equiv_refl : b.equiv b (Equiv.refl ι) = LinearEquiv.refl R M :=
  b.ext' fun i => by simp

@[simp]
/-
**Module.Basis.equiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：equiv_symm : (b.equiv b' e).symm = b'.equiv b e.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext'`：ext' {f₁ f₂ : M ≃ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = 
f₂ (b i)) : f₁ = f₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Module.Basis.equiv_apply`：equiv_apply : b.equiv b' e (b i) = b' (e i)
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equiv_symm : (b.equiv b' e).symm = b'.equiv b e.symm :=
  b'.ext' fun i => (b.equiv b' e).injective (by simp)

@[simp]
/-
**Module.Basis.equiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：equiv_trans {ι'' : Type*} (b'' : Basis ι'' R M'') (e : ι ≃ ι') (e' : ι' ≃ 
ι'') : (b.equiv b' e).trans (b'.equiv b'' e') = b.equiv b'' (e.trans e')
参数：b'' : Basis ι'' R M''；e : ι ≃ ι'；e' : ι' ≃ ι''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext'`：ext' {f₁ f₂ : M ≃ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = 
f₂ (b i)) : f₁ = f₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.equiv_apply`：equiv_apply : b.equiv b' e (b i) = b' (e i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equiv_trans {ι'' : Type*} (b'' : Basis ι'' R M'') (e : ι ≃ ι') (e' : ι' ≃ ι'') :
    (b.equiv b' e).trans (b'.equiv b'' e') = b.equiv b'' (e.trans e') :=
  b.ext' fun i => by simp

@[simp]
/-
**Module.Basis.map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：map_equiv (b : Basis ι R M) (b' : Basis ι' R M') (e : ι ≃ ι') : b.map (b.e
quiv b' e) = b'.reindex e.symm
参数：b : Basis ι R M；b' : Basis ι' R M'；e : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.eq_of_apply_eq`：eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (for
all i, b₁ i = b₂ i) -> b₁ = b₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.equiv_apply`：equiv_apply : b.equiv b' e (b i) = b' (e i)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_equiv (b : Basis ι R M) (b' : Basis ι' R M') (e : ι ≃ ι') :
    b.map (b.equiv b' e) = b'.reindex e.symm := by
  ext i
  simp

section CommSemiring

variable {R M M' : Type*} [CommSemiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
variable (b : Basis ι R M) (b' : Basis ι' R M')
variable [SMulCommClass R R M']

/-- If `b` is a basis for `M` and `b'` a basis for `M'`,
and `f`, `g` form a bijection between the basis vectors,
`b.equiv' b' f g hf hg hgf hfg` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `f (b i)`.
-/
/-
**Module.Basis.equiv'** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：equiv' (f : M -> M') (g : M' -> M) (hf : forall i, f (b i) in range b') (h
g : forall i, g (b' i) in range b) (hgf : forall i, g (f (b i)) = b i) (hfg : fo
rall i, f (g (b' i)) = b' i) : M ≃ₗ[R] M'
参数：f : M -> M'；g : M' -> M；hf : forall i, f (b i) in range b'；hg : forall i, g (
b' i) in range b；hgf : forall i, g (f (b i)) = b i；hfg : forall i, f (g (b' i)) 
= b' i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `b` is a basis for `M` and `b'` a basis for `M'`,
and `f`, `g` form a bijection between the basis vectors,
`b.equiv' b' f g hf hg hgf hfg` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b
 i` to `f (b i)`.
-/
def equiv' (f : M → M') (g : M' → M) (hf : ∀ i, f (b i) ∈ range b') (hg : ∀ i, g (b' i) ∈ range b)
    (hgf : ∀ i, g (f (b i)) = b i) (hfg : ∀ i, f (g (b' i)) = b' i) : M ≃ₗ[R] M' :=
  { constr (M' := M') b R (f ∘ b) with
    invFun := constr (M' := M) b' R (g ∘ b')
    left_inv :=
      have : (constr (M' := M) b' R (g ∘ b')).comp (constr (M' := M') b R (f ∘ b)) = LinearMap.id :=
        b.ext fun i =>
          Exists.elim (hf i) fun i' hi' => by
            rw [LinearMap.comp_apply, b.constr_basis, Function.comp_apply, ← hi', b'.constr_basis,
              Function.comp_apply, hi', hgf, LinearMap.id_apply]
      fun x => congr_arg (fun h : M →ₗ[R] M => h x) this
    right_inv :=
      have : (constr (M' := M') b R (f ∘ b)).comp (constr (M' := M) b' R (g ∘ b')) = LinearMap.id :=
        b'.ext fun i =>
          Exists.elim (hg i) fun i' hi' => by
            rw [LinearMap.comp_apply, b'.constr_basis, Function.comp_apply, ← hi', b.constr_basis,
              Function.comp_apply, hi', hfg, LinearMap.id_apply]
      fun x => congr_arg (fun h : M' →ₗ[R] M' => h x) this }

@[simp]
/-
**Module.Basis.equiv'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι' : Type u_2} {ι : Type u_10} {R : Type u_14} {M : Type u_15} {M' : Ty
pe u_16} [inst : CommSemiring R]   [inst_1 : AddCommMonoid M] [inst_2 : _root_.M
odule R M] [inst_3 : AddCommMonoid M'] [inst_4 : _root_.Module R M']   (b : Modu
le.Basis ι R M) (b' : Module.Basis ι' R M') [inst_5 : SMulCommClass R R M'] (f :
 M → M') (g : M' → M)   (hf : ∀ (i : ι), f (b i) ∈ Set.range ⇑b') (hg : ∀ (i : ι
'), g (b' i) ∈ Set.range ⇑b)   (hgf : ∀ (i : ι), g (f (b i)) = b i) (hfg : ∀ (i 
: ι'), f (g (b' i)) = b' i) (i : ι),   (b.equiv' b' f g hf hg hgf hfg) (b i) = f
 (b i)
参数：b : Module.Basis ι R M；b' : Module.Basis ι' R M'；f : M → M'；g : M' → M；hf : ∀
 (i : ι), f (b i) ∈ Set.range ⇑b'；hg : ∀ (i : ι'), g (b' i) ∈ Set.range ⇑b；hgf :
 ∀ (i : ι), g (f (b i)) = b i；hfg : ∀ (i : ι'), f (g (b' i)) = b' i；i : ι；b.equi
v' b' f g hf hg hgf hfg；b i；b i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.constr_basis`：constr_basis (f : ι -> M') (i : ι) : (constr 
(M'
-/
theorem equiv'_apply (f : M → M') (g : M' → M) (hf hg hgf hfg) (i : ι) :
    b.equiv' b' f g hf hg hgf hfg (b i) = f (b i) :=
  b.constr_basis R _ _

@[simp]
/-
**Module.Basis.equiv'_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι' : Type u_2} {ι : Type u_10} {R : Type u_14} {M : Type u_15} {M' : Ty
pe u_16} [inst : CommSemiring R]   [inst_1 : AddCommMonoid M] [inst_2 : _root_.M
odule R M] [inst_3 : AddCommMonoid M'] [inst_4 : _root_.Module R M']   (b : Modu
le.Basis ι R M) (b' : Module.Basis ι' R M') [inst_5 : SMulCommClass R R M'] (f :
 M → M') (g : M' → M)   (hf : ∀ (i : ι), f (b i) ∈ Set.range ⇑b') (hg : ∀ (i : ι
'), g (b' i) ∈ Set.range ⇑b)   (hgf : ∀ (i : ι), g (f (b i)) = b i) (hfg : ∀ (i 
: ι'), f (g (b' i)) = b' i) (i : ι'),   (b.equiv' b' f g hf hg hgf hfg).symm (b'
 i) = g (b' i)
参数：b : Module.Basis ι R M；b' : Module.Basis ι' R M'；f : M → M'；g : M' → M；hf : ∀
 (i : ι), f (b i) ∈ Set.range ⇑b'；hg : ∀ (i : ι'), g (b' i) ∈ Set.range ⇑b；hgf :
 ∀ (i : ι), g (f (b i)) = b i；hfg : ∀ (i : ι'), f (g (b' i)) = b' i；i : ι'；b.equ
iv' b' f g hf hg hgf hfg；b' i；b' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.constr_basis`：constr_basis (f : ι -> M') (i : ι) : (constr 
(M'
-/
theorem equiv'_symm_apply (f : M → M') (g : M' → M) (hf hg hgf hfg) (i : ι') :
    (b.equiv' b' f g hf hg hgf hfg).symm (b' i) = g (b' i) :=
  b'.constr_basis R _ _

set_option backward.isDefEq.respectTransparency false in
/-
**Module.Basis.sum_repr_mul_repr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：sum_repr_mul_repr {ι'} [Fintype ι'] (b' : Basis ι' R M) (x : M) (i : ι) : 
(∑ j : ι', b.repr (b' j) i * b'.repr x j) = b.repr x i
参数：b' : Basis ι' R M；x : M；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Finset.sum_apply'`：Finset.sum_apply' : (∑ k in s, f k) i = ∑ k in s, f k
 i
· 使用定理 `Finsupp.smul_apply`：smul_apply [Zero M] [SMulZeroClass R M] (b : R) (v :
 α ->₀ M) (a : α) : (b • v) a = b • v a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem sum_repr_mul_repr {ι'} [Fintype ι'] (b' : Basis ι' R M) (x : M) (i : ι) :
    (∑ j : ι', b.repr (b' j) i * b'.repr x j) = b.repr x i := by
  conv_rhs => rw [← b'.sum_repr x]
  simp_rw [map_sum, map_smul, Finset.sum_apply']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm]

end CommSemiring

end Equiv

section Coord

variable (i : ι)

/-- `b.coord i` is the linear function giving the `i`-th coordinate of a vector
with respect to the basis `b`.

`b.coord i` is an element of the dual space. In particular, for
finite-dimensional spaces it is the `ι`th basis vector of the dual space.
-/
@[simps!]
/-
**Module.Basis.coord** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：coord : M ->ₗ[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`b.coord i` is the linear function giving the `i`-th coordinate of a vector
with respect to the basis `b`.

`b.coord i` is an element of the dual space. In particular, for
finite-dimensional spaces it is the `ι`th basis vector of the dual space.
-/
def coord : M →ₗ[R] R :=
  Finsupp.lapply i ∘ₗ ↑b.repr
/-
**Module.Basis.forall_coord_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`
。
形式化陈述：forall_coord_eq_zero_iff {x : M} : (forall i, b.coord i x = 0) ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `LinearEquiv.map_eq_zero_iff`：map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0
-/
theorem forall_coord_eq_zero_iff {x : M} : (∀ i, b.coord i x = 0) ↔ x = 0 :=
  Iff.trans (by simp only [b.coord_apply, DFunLike.ext_iff, Finsupp.zero_apply])
    b.repr.map_eq_zero_iff

/-- The sum of the coordinates of an element `m : M` with respect to a basis. -/
/-
**Module.Basis.sumCoords** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：sumCoords : M ->ₗ[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of the coordinates of an element `m : M` with respect to a basis.
-/
noncomputable def sumCoords : M →ₗ[R] R :=
  (Finsupp.lsum ℕ fun _ => LinearMap.id) ∘ₗ (b.repr : M →ₗ[R] ι →₀ R)

@[simp]
/-
**Module.Basis.coe_sumCoords** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_sumCoords : (b.sumCoords : M -> R) = fun m => (b.repr m).sum fun _ => 
id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sumCoords : (b.sumCoords : M → R) = fun m => (b.repr m).sum fun _ => id :=
  rfl

@[simp high]
/-
**Module.Basis.coe_sumCoords_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`
。
形式化陈述：coe_sumCoords_of_fintype [Fintype ι] : (b.sumCoords : M -> R) = ∑ i, b.coo
rd i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Fintype.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [i
nst : Fintype ι] [inst_1 : (a : α) → AddCommMonoid (M a)] (a : α)   (g : ι → (a 
: α) → …
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
-/
theorem coe_sumCoords_of_fintype [Fintype ι] : (b.sumCoords : M → R) = ∑ i, b.coord i := by
  ext m
  simp only [sumCoords, Finsupp.sum_fintype, LinearMap.id_coe, LinearEquiv.coe_coe, coord_apply,
    id, Fintype.sum_apply, imp_true_iff, Finsupp.coe_lsum, LinearMap.coe_comp, comp_apply,
    LinearMap.coe_sum]

@[simp]
/-
**Module.Basis.sumCoords_self_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：sumCoords_self_apply : b.sumCoords (b i) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumCoords_self_apply : b.sumCoords (b i) = 1 := by
  simp only [Basis.sumCoords, LinearMap.id_coe, LinearEquiv.coe_coe, id, Basis.repr_self,
    Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp, Finsupp.sum_single_index]
/-
**Module.Basis.dvd_coord_smul** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：dvd_coord_smul (i : ι) (m : M) (r : R) : r ∣ b.coord i (r • m)
参数：i : ι；m : M；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dvd_coord_smul (i : ι) (m : M) (r : R) : r ∣ b.coord i (r • m) :=
  ⟨b.coord i m, by simp⟩
/-
**Module.Basis.coord_repr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coord_repr_symm (b : Basis ι R M) (i : ι) (f : ι ->₀ R) : b.coord i (b.rep
r.symm f) = f i
参数：b : Basis ι R M；i : ι；f : ι ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `Module.Basis.repr_linearCombination`：repr_linearCombination (v) : b.repr
 (Finsupp.linearCombination _ b v) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coord_repr_symm (b : Basis ι R M) (i : ι) (f : ι →₀ R) :
    b.coord i (b.repr.symm f) = f i := by
  simp only [repr_symm_apply, coord_apply, repr_linearCombination]
/-
**Module.Basis.coe_sumCoords_eq_finsum** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_sumCoords_eq_finsum : (b.sumCoords : M -> R) = fun m => ∑ᶠ i, b.coord 
i m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.hasFiniteSupport`：hasFiniteSupport (f : α ->₀ M) : HasFiniteSupp
ort f
· 使用定理 `finsum_eq_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] 
(f : α → M) (hf : Function.HasFiniteSupport f),   ∑ᶠ (i : α), f i = ∑ i ∈ Set.Fi
nit…
· 使用定理 `Finsupp.fun_support_eq`：fun_support_eq (f : α ->₀ M) : Function.support 
f = f.support
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
· 使用定理 `Finset.finite_toSet_toFinset`：finite_toSet_toFinset (s : Finset α) : s.f
inite_toSet.toFinset = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_sumCoords_eq_finsum : (b.sumCoords : M → R) = fun m => ∑ᶠ i, b.coord i m := by
  ext m
  simp only [Basis.sumCoords, Basis.coord, Finsupp.lapply_apply, LinearMap.id_coe,
    LinearEquiv.coe_coe, Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp,
    finsum_eq_sum _ (b.repr m).hasFiniteSupport, Finsupp.sum, Finset.finite_toSet_toFinset, id,
    Finsupp.fun_support_eq]

variable (e : ι ≃ ι')

@[simp]
/-
**Module.Basis.sumCoords_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：sumCoords_reindex : (b.reindex e).sumCoords = b.sumCoords
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.repr_reindex`：repr_reindex : (b.reindex e).repr x = (b.repr
 x).mapDomain e
· 使用定理 `Finsupp.sum_mapDomain_index`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f : α 
→ β} {s : α →₀ M}…
-/
theorem sumCoords_reindex : (b.reindex e).sumCoords = b.sumCoords := by
  ext x
  simp only [coe_sumCoords, repr_reindex]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) fun _ _ _ => rfl

variable (S : Type*) [Semiring S] [Module S M']
variable [SMulCommClass R S M']
/-
**Module.Basis.coord_equivFun_symm** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coord_equivFun_symm [Finite ι] (b : Basis ι R M) (i : ι) (f : ι -> R) : b.
coord i (b.equivFun.symm f) = f i
参数：b : Basis ι R M；i : ι；f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.coord_repr_symm`：coord_repr_symm (b : Basis ι R M) (i : ι) 
(f : ι ->₀ R) : b.coord i (b.repr.symm f) = f i
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coord_equivFun_symm [Finite ι] (b : Basis ι R M) (i : ι) (f : ι → R) :
    b.coord i (b.equivFun.symm f) = f i :=
  b.coord_repr_symm i (Finsupp.equivFunOnFinite.symm f)

end Coord

end Basis

end Module

