/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
module

public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Data.Multiset.Find

/-!
# Type of functions with finite support

For any type `α` and any type `M` with zero, we define the type `Finsupp α M` (notation: `α →₀ M`)
of finitely supported functions from `α` to `M`, i.e. the functions which are zero everywhere
on `α` except on a finite set.

Functions with finite support are used (at least) in the following parts of the library:

* `MonoidAlgebra R M` and `AddMonoidAlgebra R M` are defined as `M →₀ R`;

* polynomials and multivariate polynomials are defined as `AddMonoidAlgebra`s, hence they use
  `Finsupp` under the hood;

* the linear combination of a family of vectors `v i` with coefficients `f i` (as used, e.g., to
  define linearly independent family `LinearIndependent`) is defined as a map
  `Finsupp.linearCombination : (ι → M) → (ι →₀ R) →ₗ[R] M`.

Some other constructions are naturally equivalent to `α →₀ M` with some `α` and `M` but are defined
in a different way in the library:

* `Multiset α ≃+ α →₀ ℕ`;
* `FreeAbelianGroup α ≃+ α →₀ ℤ`.

Most of the theory assumes that the range is a commutative additive monoid. This gives us the big
sum operator as a powerful way to construct `Finsupp` elements, which is defined in
`Mathlib/Algebra/BigOperators/Finsupp/Basic.lean`.

Many constructions based on `α →₀ M` are `def`s rather than `abbrev`s to avoid reusing unwanted type
class instances. E.g., `MonoidAlgebra`, `AddMonoidAlgebra`, and types based on these two have
non-pointwise multiplication.

## Main declarations

* `Finsupp`: The type of finitely supported functions from `α` to `β`.
* `Finsupp.onFinset`: The restriction of a function to a `Finset` as a `Finsupp`.
* `Finsupp.mapRange`: Composition of a `ZeroHom` with a `Finsupp`.
* `Finsupp.embDomain`: Maps the domain of a `Finsupp` by an embedding.
* `Finsupp.zipWith`: Postcomposition of two `Finsupp`s with a function `f` such that `f 0 0 = 0`.

## Notation

This file adds `α →₀ M` as a global notation for `Finsupp α M`.

We also use the following convention for `Type*` variables in this file

* `α`, `β`: types with no additional structure that appear as the first argument to `Finsupp`
  somewhere in the statement;

* `ι` : an auxiliary index type;

* `M`, `N`, `O`: types with `Zero` or `(Add)(Comm)Monoid` structure;

* `G`, `H`: groups (commutative or not, multiplicative or additive);

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

## TODO

* Expand the list of definitions and important lemmas to the module docstring.

-/

@[expose] public section

assert_not_exists CompleteLattice Monoid

noncomputable section

open Finset Function

variable {α β ι M N O G H : Type*}

/-- `Finsupp α M`, denoted `α →₀ M`, is the type of functions `f : α → M` such that
  `f x = 0` for all but finitely many `x`. -/
/-
**Finsupp** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_9 → (M : Type u_10) → [Zero M] → Type (max u_10 u_9)
参数：M : Type u_10；max u_10 u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finsupp α M`, denoted `α →₀ M`, is the type of functions `f : α → M` such that
  `f x = 0` for all but finitely many `x`.
-/
structure Finsupp (α : Type*) (M : Type*) [Zero M] where
  /-- The support of a finitely supported function (aka `Finsupp`). -/
  support : Finset α
  /-- The underlying function of a bundled finitely supported function (aka `Finsupp`). -/
  toFun : α → M
  /-- The witness that the support of a `Finsupp` is indeed the exact locus where its
  underlying function is nonzero. -/
  mem_support_toFun : ∀ a, a ∈ support ↔ toFun a ≠ 0

@[inherit_doc]
infixr:25 " →₀ " => Finsupp

namespace Finsupp

/-! ### Basic declarations about `Finsupp` -/


section Basic

variable [Zero M]

/-
**Finsupp.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instFunLike : FunLike (α ->₀ M) α M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (α →₀ M) α M :=
  ⟨toFun, by
    rintro ⟨s, f, hf⟩ ⟨t, g, hg⟩ (rfl : f = g)
    congr
    ext a
    exact (hf _).trans (hg _).symm⟩

initialize_simps_projections Finsupp (toFun → apply)

@[ext, grind ext]
/-
**Finsupp.ext** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : α →₀ M} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h
/-
**Finsupp.instSubsingleton** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instSubsingleton [IsEmpty α] : Subsingleton (α ->₀ M) where allEq f g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
instance instSubsingleton [IsEmpty α] : Subsingleton (α →₀ M) where
  allEq f g := by ext x; exact isEmptyElim x
/-
**Finsupp.instSubsingleton'** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instSubsingleton' [Subsingleton M] : Subsingleton (α ->₀ M) where allEq f 
g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance instSubsingleton' [Subsingleton M] : Subsingleton (α →₀ M) where
  allEq f g := by ext x; exact Subsingleton.elim ..

variable (α) in
/-
**Finsupp.nontrivial_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：nontrivial_of_nontrivial [h : Nontrivial (α ->₀ M)] : Nontrivial M
参数：α ->₀ M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem nontrivial_of_nontrivial [h : Nontrivial (α →₀ M)] : Nontrivial M := by
  contrapose! h; infer_instance
/-
**Finsupp.ne_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：ne_iff {f g : α ->₀ M} : f != g ↔ exists a, f a != g a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ne_iff`：ne_iff {f g : F} : f != g ↔ exists a, f a != g a
-/
lemma ne_iff {f g : α →₀ M} : f ≠ g ↔ ∃ a, f a ≠ g a := DFunLike.ne_iff

@[simp, norm_cast, grind =]
/-
**Finsupp.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：coe_mk (f : α -> M) (s : Finset α) (h : forall a, a in s ↔ f a != 0) : ⇑(⟨
s, f, h⟩ : α ->₀ M) = f
参数：f : α -> M；s : Finset α；h : forall a, a in s ↔ f a != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : α → M) (s : Finset α) (h : ∀ a, a ∈ s ↔ f a ≠ 0) : ⇑(⟨s, f, h⟩ : α →₀ M) = f :=
  rfl
/-
**Finsupp.instZero** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instZero : Zero (α ->₀ M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero (α →₀ M) :=
  ⟨⟨∅, 0, fun _ => ⟨fun h ↦ (notMem_empty _ h).elim, fun H => (H rfl).elim⟩⟩⟩
/-
**Finsupp.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M], ⇑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_zero : ⇑(0 : α →₀ M) = 0 := rfl

@[grind =]
/-
**Finsupp.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：zero_apply {a : α} : (0 : α ->₀ M) a = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply {a : α} : (0 : α →₀ M) a = 0 :=
  rfl

@[simp, grind =]
/-
**Finsupp.support_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_zero : (0 : α ->₀ M).support = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_zero : (0 : α →₀ M).support = ∅ :=
  rfl
/-
**Finsupp.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instInhabited : Inhabited (α ->₀ M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (α →₀ M) :=
  ⟨0⟩
/-
**Finsupp.default_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M], default = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma default_eq_zero : (default : α →₀ M) = 0 := rfl

@[simp, grind =]
/-
**Finsupp.mem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_support_iff {f : α ->₀ M} : forall {a : α}, a in f.support ↔ f a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.mem_support_toFun`：∀ {α : Type u_9} {M : Type u_10} [inst : Zero
 M] (self : α →₀ M) (a : α), a ∈ self.support ↔ self.toFun a ≠ 0
-/
theorem mem_support_iff {f : α →₀ M} : ∀ {a : α}, a ∈ f.support ↔ f a ≠ 0 :=
  @(f.mem_support_toFun)

@[simp, norm_cast]
/-
**Finsupp.fun_support_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：fun_support_eq (f : α ->₀ M) : Function.support f = f.support
参数：f : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
-/
theorem fun_support_eq (f : α →₀ M) : Function.support f = f.support :=
  Set.ext fun _x => mem_support_iff.symm
/-
**Finsupp.notMem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f.support ↔ f a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
-/
theorem notMem_support_iff {f : α →₀ M} {a} : a ∉ f.support ↔ f a = 0 :=
  not_iff_comm.1 mem_support_iff.symm

@[simp, norm_cast]
/-
**Finsupp.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：coe_eq_zero {f : α ->₀ M} : (f : α -> M) = 0 ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.coe_zero`：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M], ⇑0 = 
0
· 使用定理 `DFunLike.coe_fn_eq`：coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g :
 forall a : α, β a) ↔ f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_eq_zero {f : α →₀ M} : (f : α → M) = 0 ↔ f = 0 := by rw [← coe_zero, DFunLike.coe_fn_eq]
/-
**Finsupp.ext_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：ext_iff' {f g : α ->₀ M} : f = g ↔ f.support = g.support ∧ forall x in f.s
upport, f x = g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ext_iff' {f g : α →₀ M} : f = g ↔ f.support = g.support ∧ ∀ x ∈ f.support, f x = g x :=
  ⟨fun h => h ▸ ⟨rfl, fun _ _ => rfl⟩, fun ⟨h₁, h₂⟩ =>
    ext fun a => by
      classical
      exact if h : a ∈ f.support then h₂ a h else by
        have hf : f a = 0 := notMem_support_iff.1 h
        have hg : g a = 0 := by rwa [h₁, notMem_support_iff] at h
        rw [hf, hg]⟩

@[simp]
/-
**Finsupp.support_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_eq_empty {f : α ->₀ M} : f.support = ∅ ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.fun_support_eq`：fun_support_eq (f : α ->₀ M) : Function.support 
f = f.support
· 使用定理 `Function.support_eq_empty_iff`：∀ {ι : Type u_1} {M : Type u_3} [inst : Z
ero M] {f : ι → M}, Function.support f = ∅ ↔ f = 0
-/
theorem support_eq_empty {f : α →₀ M} : f.support = ∅ ↔ f = 0 :=
  mod_cast @Function.support_eq_empty_iff _ _ _ f

@[simp]
/-
**Finsupp.support_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_nonempty_iff {f : α ->₀ M} : f.support.Nonempty ↔ f != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₃`：contrapose_iff₃ {p q : Prop} 
: (¬ p ↔ q) -> (p ↔ ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.support_eq_empty`：support_eq_empty {f : α ->₀ M} : f.support = ∅
 ↔ f = 0
-/
theorem support_nonempty_iff {f : α →₀ M} : f.support.Nonempty ↔ f ≠ 0 := by
  contrapose!; exact support_eq_empty
/-
**Finsupp.card_support_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：card_support_eq_zero {f : α ->₀ M} : #f.support = 0 ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem card_support_eq_zero {f : α →₀ M} : #f.support = 0 ↔ f = 0 := by simp
/-
**Finsupp.instDecidableEq** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instDecidableEq [DecidableEq α] [DecidableEq M] : DecidableEq (α ->₀ M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableEq [DecidableEq α] [DecidableEq M] : DecidableEq (α →₀ M) := fun f g =>
  decidable_of_iff (f.support = g.support ∧ ∀ a ∈ f.support, f a = g a) ext_iff'.symm

@[fun_prop]
/-
**Finsupp.hasFiniteSupport** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：hasFiniteSupport (f : α ->₀ M) : HasFiniteSupport f
参数：f : α ->₀ M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.HasFiniteSupport.eq_1`：∀ {α : Type u_1} {M : Type u_2} [inst : 
Zero M] (f : α → M), Function.HasFiniteSupport f = (Function.support f).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.fun_support_eq`：fun_support_eq (f : α ->₀ M) : Function.support 
f = f.support
-/
theorem hasFiniteSupport (f : α →₀ M) : HasFiniteSupport f := by
  rw [HasFiniteSupport]
  exact f.fun_support_eq.symm ▸ f.support.finite_toSet

@[deprecated (since := "2026-03-03")] alias finite_support := hasFiniteSupport
/-
**Finsupp.support_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_subset_iff {s : Set α} {f : α ->₀ M} : ↑f.support subseteq s ↔ for
all a ∉ s, f a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_subset_iff {s : Set α} {f : α →₀ M} :
    ↑f.support ⊆ s ↔ ∀ a ∉ s, f a = 0 := by
  grind

/-- Given `Finite α`, `equivFunOnFinite` is the `Equiv` between `α →₀ β` and `α → β`.
  (All functions on a finite type are finitely supported.) -/
@[simps]
/-
**Finsupp.equivFunOnFinite** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：equivFunOnFinite [Finite α] : (α ->₀ M) ≃ (α -> M) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `Finite α`, `equivFunOnFinite` is the `Equiv` between `α →₀ β` and `α → β`
.
  (All functions on a finite type are finitely supported.)
-/
def equivFunOnFinite [Finite α] : (α →₀ M) ≃ (α → M) where
  toFun := (⇑)
  invFun f := mk (Function.support f).toFinite.toFinset f fun _a => Set.Finite.mem_toFinset _

@[simp]
/-
**Finsupp.equivFunOnFinite_symm_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：equivFunOnFinite_symm_coe {α} [Finite α] (f : α ->₀ M) : equivFunOnFinite.
symm f = f
参数：f : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem equivFunOnFinite_symm_coe {α} [Finite α] (f : α →₀ M) : equivFunOnFinite.symm f = f :=
  equivFunOnFinite.symm_apply_apply f

@[simp]
/-
**Finsupp.coe_equivFunOnFinite_symm** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：coe_equivFunOnFinite_symm {α} [Finite α] (f : α -> M) : ⇑(equivFunOnFinite
.symm f) = f
参数：f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma coe_equivFunOnFinite_symm {α} [Finite α] (f : α → M) : ⇑(equivFunOnFinite.symm f) = f := rfl

@[ext]
/-
**Finsupp.unique_ext** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：unique_ext [Unique α] {f g : α ->₀ M} (h : f default = g default) : f = g
参数：h : f default = g default。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
-/
theorem unique_ext [Unique α] {f g : α →₀ M} (h : f default = g default) : f = g :=
  ext fun a => by rwa [Unique.eq_default a]

end Basic

/-! ### Declarations about `onFinset` -/


section OnFinset

variable [Zero M]

/-- The (not exposed) support of `Finsupp.onFinset`. -/
/-
**Finsupp.onFinsetSupport** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：{α : Type u_1} → {M : Type u_4} → [Zero M] → Finset α → (α → M) → Finset α
参数：α → M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (not exposed) support of `Finsupp.onFinset`.
-/
@[no_expose] def onFinsetSupport (s : Finset α) (f : α → M) : Finset α :=
  haveI := Classical.decEq M
  {a ∈ s | f a ≠ 0}

/-- `Finsupp.onFinset s f hf` is the finsupp function representing `f` restricted to the finset `s`.
The function must be `0` outside of `s`. Use this when the set needs to be filtered anyways,
otherwise a better set representation is often available. -/
/-
**Finsupp.onFinset** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：onFinset (s : Finset α) (f : α -> M) (hf : forall a, f a != 0 -> a in s) :
 α ->₀ M where support
参数：s : Finset α；f : α -> M；hf : forall a, f a != 0 -> a in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finsupp.onFinset s f hf` is the finsupp function representing `f` restricted to
 the finset `s`.
The function must be `0` outside of `s`. Use this when the set needs to be filte
red anyways,
otherwise a better set representation is often available.
-/
def onFinset (s : Finset α) (f : α → M) (hf : ∀ a, f a ≠ 0 → a ∈ s) : α →₀ M where
  support := onFinsetSupport s f
  toFun := f
  mem_support_toFun := by simpa [onFinsetSupport]
/-
**Finsupp.coe_onFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M] (s : Finset α) (f : α → M)
 (hf : ∀ (a : α), f a ≠ 0 → a ∈ s),   ⇑(Finsupp.onFinset s f hf) = f
参数：s : Finset α；f : α → M；hf : ∀ (a : α), f a ≠ 0 → a ∈ s；Finsupp.onFinset s f h
f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_onFinset (s : Finset α) (f : α → M) (hf) : onFinset s f hf = f := rfl

@[simp, grind =]
/-
**Finsupp.onFinset_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：onFinset_apply {s : Finset α} {f : α -> M} {hf a} : (onFinset s f hf : α -
>₀ M) a = f a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem onFinset_apply {s : Finset α} {f : α → M} {hf a} : (onFinset s f hf : α →₀ M) a = f a :=
  rfl
/-
**Finsupp.support_onFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_onFinset [DecidableEq M] {s : Finset α} {f : α -> M} (hf : forall 
a : α, f a != 0 -> a in s) : (Finsupp.onFinset s f hf).support = {a in s | f a !
= 0}
参数：hf : forall a : α, f a != 0 -> a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Data.Finsupp.Defs.0.Finsupp.onFinsetSupport.eq_1`：∀ {α 
: Type u_1} {M : Type u_4} [inst : Zero M] (s : Finset α) (f : α → M),   Finsupp
.onFinsetSupport s f = {a ∈ s | f a ≠ 0}
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
theorem support_onFinset [DecidableEq M] {s : Finset α} {f : α → M}
    (hf : ∀ a : α, f a ≠ 0 → a ∈ s) :
    (Finsupp.onFinset s f hf).support = {a ∈ s | f a ≠ 0} := by
  dsimp [onFinset]; rw [onFinsetSupport]; congr
/-
**Finsupp.onFinset_support** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M] (f : α →₀ M), Finsupp.onFi
nset f.support ⇑f ⋯ = f
参数：f : α →₀ M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma onFinset_support (f : α →₀ M) : onFinset f.support f (by simp) = f := by ext; simp

@[simp]
/-
**Finsupp.support_onFinset_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_onFinset_subset {s : Finset α} {f : α -> M} {hf} : (onFinset s f h
f).support subseteq s
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_onFinset_subset {s : Finset α} {f : α → M} {hf} :
    (onFinset s f hf).support ⊆ s := by
  grind

grind_pattern support_onFinset_subset => onFinset s f hf
/-
**Finsupp.mem_support_onFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_support_onFinset {s : Finset α} {f : α -> M} (hf : forall a : α, f a !
= 0 -> a in s) {a : α} : a in (Finsupp.onFinset s f hf).support ↔ f a != 0
参数：hf : forall a : α, f a != 0 -> a in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Finsupp.onFinset_apply`：onFinset_apply {s : Finset α} {f : α -> M} {hf a
} : (onFinset s f hf : α ->₀ M) a = f a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_support_onFinset {s : Finset α} {f : α → M} (hf : ∀ a : α, f a ≠ 0 → a ∈ s) {a : α} :
    a ∈ (Finsupp.onFinset s f hf).support ↔ f a ≠ 0 := by
  rw [Finsupp.mem_support_iff, Finsupp.onFinset_apply]

end OnFinset

section OfSupportFinite

variable [Zero M]

/-- The natural `Finsupp` induced by the function `f` given that it has finite support. -/
/-
**Finsupp.ofSupportFinite** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：ofSupportFinite (f : α -> M) (hf : (Function.support f).Finite) : α ->₀ M 
where support
参数：f : α -> M；hf : (Function.support f).Finite。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural `Finsupp` induced by the function `f` given that it has finite suppo
rt.
-/
noncomputable def ofSupportFinite (f : α → M) (hf : (Function.support f).Finite) : α →₀ M where
  support := hf.toFinset
  toFun := f
  mem_support_toFun _ := hf.mem_toFinset
/-
**Finsupp.ofSupportFinite_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：ofSupportFinite_coe {f : α -> M} {hf : (Function.support f).Finite} : (ofS
upportFinite f hf : α -> M) = f
参数：Function.support f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSupportFinite_coe {f : α → M} {hf : (Function.support f).Finite} :
    (ofSupportFinite f hf : α → M) = f :=
  rfl
/-
**Finsupp.ofSupportFinite_support** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：ofSupportFinite_support {f : α -> M} (hf : f.support.Finite) : (ofSupportF
inite f hf).support = hf.toFinset
参数：hf : f.support.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ofSupportFinite_support {f : α → M} (hf : f.support.Finite) :
    (ofSupportFinite f hf).support = hf.toFinset := by
  ext; simp [ofSupportFinite_coe]
/-
**Finsupp.instCanLift** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instCanLift : CanLift (α -> M) (α ->₀ M) (⇑) fun f => (Function.support f)
.Finite where prf f hf
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCanLift : CanLift (α → M) (α →₀ M) (⇑) fun f => (Function.support f).Finite where
  prf f hf := ⟨ofSupportFinite f hf, rfl⟩

end OfSupportFinite

/-! ### Declarations about `mapRange` -/


section MapRange

variable [Zero M] [Zero N] [Zero O]

/-- The composition of `f : M → N` and `g : α →₀ M` is `mapRange f hf g : α →₀ N`,
which is well-defined when `f 0 = 0`.

This preserves the structure on `f`, and exists in various bundled forms for when `f` is itself
bundled (defined in `Mathlib/Data/Finsupp/Basic.lean`):

* `Finsupp.mapRange.equiv`
* `Finsupp.mapRange.zeroHom`
* `Finsupp.mapRange.addMonoidHom`
* `Finsupp.mapRange.addEquiv`
* `Finsupp.mapRange.linearMap`
* `Finsupp.mapRange.linearEquiv`
-/
/-
**Finsupp.mapRange** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：mapRange (f : M -> N) (hf : f 0 = 0) (g : α ->₀ M) : α ->₀ N
参数：f : M -> N；hf : f 0 = 0；g : α ->₀ M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of `f : M → N` and `g : α →₀ M` is `mapRange f hf g : α →₀ N`,
which is well-defined when `f 0 = 0`.

This preserves the structure on `f`, and exists in various bundled forms for whe
n `f` is itself
bundled (defined in `Mathlib/Data/Finsupp/Basic.lean`):

* `Finsupp.mapRange.equiv`
* `Finsupp.mapRange.zeroHom`
* `Finsupp.mapRange.addMonoidHom`
* `Finsupp.mapRange.addEquiv`
* `Finsupp.mapRange.linearMap`
* `Finsupp.mapRange.linearEquiv`
-/
def mapRange (f : M → N) (hf : f 0 = 0) (g : α →₀ M) : α →₀ N :=
  onFinset g.support (f ∘ g) fun a => by
    rw [mem_support_iff, not_imp_not]; exact fun H => (congr_arg f H).trans hf

@[simp, grind =]
/-
**Finsupp.mapRange_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_apply {f : M -> N} {hf : f 0 = 0} {g : α ->₀ M} {a : α} : mapRang
e f hf g a = f (g a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapRange_apply {f : M → N} {hf : f 0 = 0} {g : α →₀ M} {a : α} :
    mapRange f hf g a = f (g a) :=
  rfl

@[simp]
/-
**Finsupp.mapRange_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_zero {f : M -> N} {hf : f 0 = 0} : mapRange f hf (0 : α ->₀ M) = 
0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapRange_zero {f : M → N} {hf : f 0 = 0} : mapRange f hf (0 : α →₀ M) = 0 :=
  ext fun _ => by simp only [hf, zero_apply, mapRange_apply]

@[simp]
/-
**Finsupp.mapRange_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_eq_zero {a : α ->₀ M} {f : M -> N} (hf : f.Injective) (h) : mapRa
nge f h a = 0 ↔ a = 0
参数：hf : f.Injective；h。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mapRange_eq_zero {a : α →₀ M} {f : M → N} (hf : f.Injective) (h) :
    mapRange f h a = 0 ↔ a = 0 := by
  simp [Finsupp.ext_iff, ← h, hf.eq_iff]

@[simp]
/-
**Finsupp.mapRange_id** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_id (g : α ->₀ M) : mapRange id rfl g = g
参数：g : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem mapRange_id (g : α →₀ M) : mapRange id rfl g = g :=
  ext fun _ => rfl
/-
**Finsupp.mapRange_comp** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_comp (f : N -> O) (hf : f 0 = 0) (f₂ : M -> N) (hf₂ : f₂ 0 = 0) (
h : (f ∘ f₂) 0 = 0) (g : α ->₀ M) : mapRange (f ∘ f₂) h g = mapRange f hf (mapRa
nge f₂ hf₂ g)
参数：f : N -> O；hf : f 0 = 0；f₂ : M -> N；hf₂ : f₂ 0 = 0；h : (f ∘ f₂) 0 = 0；g : α -
>₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem mapRange_comp (f : N → O) (hf : f 0 = 0) (f₂ : M → N) (hf₂ : f₂ 0 = 0) (h : (f ∘ f₂) 0 = 0)
    (g : α →₀ M) : mapRange (f ∘ f₂) h g = mapRange f hf (mapRange f₂ hf₂ g) :=
  ext fun _ => rfl

@[simp]
/-
**Finsupp.mapRange_mapRange** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_mapRange (e₁ : N -> O) (e₂ : M -> N) (he₁ he₂) (f : α ->₀ M) : ma
pRange e₁ he₁ (mapRange e₂ he₂ f) = mapRange (e₁ ∘ e₂) (by simp [*]) f
参数：e₁ : N -> O；e₂ : M -> N；he₁ he₂；f : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
lemma mapRange_mapRange (e₁ : N → O) (e₂ : M → N) (he₁ he₂) (f : α →₀ M) :
    mapRange e₁ he₁ (mapRange e₂ he₂ f) = mapRange (e₁ ∘ e₂) (by simp [*]) f := ext fun _ ↦ rfl
/-
**Finsupp.support_mapRange** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_mapRange {f : M -> N} {hf : f 0 = 0} {g : α ->₀ M} : (mapRange f h
f g).support subseteq g.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.support_onFinset_subset`：support_onFinset_subset {s : Finset α} 
{f : α -> M} {hf} : (onFinset s f hf).support subseteq s
-/
theorem support_mapRange {f : M → N} {hf : f 0 = 0} {g : α →₀ M} :
    (mapRange f hf g).support ⊆ g.support :=
  support_onFinset_subset
/-
**Finsupp.support_mapRange_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_mapRange_of_injective {e : M -> N} (he0 : e 0 = 0) (f : ι ->₀ M) (
he : Function.Injective e) : (Finsupp.mapRange e he0 f).support = f.support
参数：he0 : e 0 = 0；f : ι ->₀ M；he : Function.Injective e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_mapRange_of_injective {e : M → N} (he0 : e 0 = 0) (f : ι →₀ M)
    (he : Function.Injective e) : (Finsupp.mapRange e he0 f).support = f.support := by grind
/-
**Finsupp.range_mapRange** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：range_mapRange (e : M -> N) (he₀ : e 0 = 0) : Set.range (Finsupp.mapRange 
(α
参数：e : M -> N；he₀ : e 0 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma range_mapRange (e : M → N) (he₀ : e 0 = 0) :
    Set.range (Finsupp.mapRange (α := α) e he₀) = {g | ∀ i, g i ∈ Set.range e} := by
  ext g
  simp only [Set.mem_range, Set.mem_ofPred]
  constructor
  · grind
  · intro h
    classical
    choose f h using h
    use onFinset g.support (fun x ↦ if x ∈ g.support then f x else 0) (by simp_all)
    grind

/-- `Finsupp.mapRange` of an injective function is injective. -/
/-
**Finsupp.mapRange_injective** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_injective (e : M -> N) (he₀ : e 0 = 0) (he : Injective e) : Injec
tive (Finsupp.mapRange (α
参数：e : M -> N；he₀ : e 0 = 0；he : Injective e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.ext_iff`：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M] {f g : 
α →₀ M}, f = g ↔ ∀ (a : α), f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b

--- 原说明 ---
`Finsupp.mapRange` of an injective function is injective.
-/
lemma mapRange_injective (e : M → N) (he₀ : e 0 = 0) (he : Injective e) :
    Injective (Finsupp.mapRange (α := α) e he₀) := by
  intro a b h
  rw [Finsupp.ext_iff] at h ⊢
  simpa only [mapRange_apply, he.eq_iff] using h

/-- `Finsupp.mapRange` of a surjective function is surjective. -/
/-
**Finsupp.mapRange_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_surjective (e : M -> N) (he₀ : e 0 = 0) (he : Surjective e) : Sur
jective (Finsupp.mapRange (α
参数：e : M -> N；he₀ : e 0 = 0；he : Surjective e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用引理 `Finsupp.range_mapRange`：range_mapRange (e : M -> N) (he₀ : e 0 = 0) : Se
t.range (Finsupp.mapRange (α
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`Finsupp.mapRange` of a surjective function is surjective.
-/
lemma mapRange_surjective (e : M → N) (he₀ : e 0 = 0) (he : Surjective e) :
    Surjective (Finsupp.mapRange (α := α) e he₀) := by
  rw [← Set.range_eq_univ, range_mapRange, he.range_eq]
  simp
/-
**Finsupp.mapRange_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_bijective (e : M -> N) (he₀ : e 0 = 0) (he : Bijective e) : Bijec
tive (Finsupp.mapRange (α
参数：e : M -> N；he₀ : e 0 = 0；he : Bijective e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.mapRange_injective`：mapRange_injective (e : M -> N) (he₀ : e 0 =
 0) (he : Injective e) : Injective (Finsupp.mapRange (α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Finsupp.mapRange_surjective`：mapRange_surjective (e : M -> N) (he₀ : e 0
 = 0) (he : Surjective e) : Surjective (Finsupp.mapRange (α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma mapRange_bijective (e : M → N) (he₀ : e 0 = 0) (he : Bijective e) :
    Bijective (Finsupp.mapRange (α := α) e he₀) :=
  ⟨mapRange_injective e he₀ he.1, mapRange_surjective e he₀ he.2⟩

end MapRange

section Equiv
variable [Zero M] [Zero N] [Zero O]

/-- `Finsupp.mapRange` as an equiv. -/
@[simps (attr := grind =) apply]
/-
**Finsupp.mapRange.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.mapRange`。
形式化陈述：{ι : Type u_3} →   {M : Type u_4} → {N : Type u_5} → [inst : Zero M] → [in
st_1 : Zero N] → (e : M ≃ N) → e 0 = 0 → (ι →₀ M) ≃ (ι →₀ N)
参数：e : M ≃ N；ι →₀ M；ι →₀ N。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`Finsupp.mapRange` as an equiv.
-/
def mapRange.equiv (e : M ≃ N) (hf : e 0 = 0) : (ι →₀ M) ≃ (ι →₀ N) where
  toFun := mapRange e hf
  invFun := mapRange e.symm <| by simp [← hf]
  left_inv x := by ext; simp
  right_inv x := by ext; simp

set_option backward.isDefEq.respectTransparency false in
/-
**Finsupp.mapRange.equiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapRange`。
形式化陈述：∀ {ι : Type u_3} {M : Type u_4} [inst : Zero M], Finsupp.mapRange.equiv (E
quiv.refl M) ⋯ = Equiv.refl (ι →₀ M)
参数：Equiv.refl M；ι →₀ M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapRange.equiv_apply`：∀ {ι : Type u_3} {M : Type u_4} {N : Type 
u_5} [inst : Zero M] [inst_1 : Zero N] (e : M ≃ N) (hf : e 0 = 0)   (g : ι →₀ M)
, (Finsupp.mapRang…
· 使用定理 `Finsupp.mapRange_id`：mapRange_id (g : α ->₀ M) : mapRange id rfl g = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mapRange.equiv_refl : mapRange.equiv (.refl M) rfl = .refl (ι →₀ M) := by ext; simp
/-
**Finsupp.mapRange.equiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapRange`。
形式化陈述：∀ {ι : Type u_3} {M : Type u_4} {N : Type u_5} {O : Type u_6} [inst : Zero
 M] [inst_1 : Zero N] [inst_2 : Zero O]   (e : M ≃ N) (hf : e 0 = 0) (f₂ : N ≃ O
) (hf₂ : f₂ 0 = 0),   Finsupp.mapRange.equiv (e.trans f₂) ⋯ = (Finsupp.mapRange.
equiv e hf).trans (Finsupp.mapRange.equiv f₂ hf₂)
参数：e : M ≃ N；hf : e 0 = 0；f₂ : N ≃ O；hf₂ : f₂ 0 = 0；e.trans f₂；Finsupp.mapRange.
equiv e hf；Finsupp.mapRange.equiv f₂ hf₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.mapRange.equiv_apply`：∀ {ι : Type u_3} {M : Type u_4} {N : Type 
u_5} [inst : Zero M] [inst_1 : Zero N] (e : M ≃ N) (hf : e 0 = 0)   (g : ι →₀ M)
, (Finsupp.mapRang…
· 使用引理 `Finsupp.mapRange_mapRange`：mapRange_mapRange (e₁ : N -> O) (e₂ : M -> N)
 (he₁ he₂) (f : α ->₀ M) : mapRange e₁ he₁ (mapRange e₂ he₂ f) = mapRange (e₁ ∘ 
e₂) (by simp [*…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapRange.equiv_trans (e : M ≃ N) (hf) (f₂ : N ≃ O) (hf₂) :
    mapRange.equiv (ι := ι) (e.trans f₂) (by rw [Equiv.trans_apply, hf, hf₂]) =
      (mapRange.equiv e hf).trans (mapRange.equiv f₂ hf₂) := by ext; simp

@[simp, grind =]
/-
**Finsupp.mapRange.equiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapRange`。
形式化陈述：∀ {ι : Type u_3} {M : Type u_4} {N : Type u_5} [inst : Zero M] [inst_1 : Z
ero N] (e : M ≃ N) (hf : e 0 = 0),   (Finsupp.mapRange.equiv e hf).symm = Finsup
p.mapRange.equiv e.symm ⋯
参数：e : M ≃ N；hf : e 0 = 0；Finsupp.mapRange.equiv e hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma mapRange.equiv_symm (e : M ≃ N) (hf) :
    (mapRange.equiv (ι := ι) e hf).symm = mapRange.equiv e.symm (by simp [← hf]) := rfl

end Equiv

/-! ### Declarations about `embDomain` -/


section EmbDomain

variable [Zero M] [Zero N]

/-- Given `f : α ↪ β` and `v : α →₀ M`, `Finsupp.embDomain f v : β →₀ M`
is the finitely supported function whose value at `f a : β` is `v a`.
For a `b : β` outside the range of `f`, it is zero. -/
/-
**Finsupp.embDomain** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：embDomain (f : α ↪ β) (v : α ->₀ M) : β ->₀ M where support
参数：f : α ↪ β；v : α ->₀ M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : α ↪ β` and `v : α →₀ M`, `Finsupp.embDomain f v : β →₀ M`
is the finitely supported function whose value at `f a : β` is `v a`.
For a `b : β` outside the range of `f`, it is zero.
-/
def embDomain (f : α ↪ β) (v : α →₀ M) : β →₀ M where
  support := v.support.map f
  toFun b :=
    haveI := Classical.decEq β
    match v.support.1.find? (fun a => f a = b) (by intro x; grind) with
    | some a => v a
    | none => 0
  mem_support_toFun a₂ := by grind

@[simp]
/-
**Finsupp.support_embDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_embDomain (f : α ↪ β) (v : α ->₀ M) : (embDomain f v).support = v.
support.map f
参数：f : α ↪ β；v : α ->₀ M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_embDomain (f : α ↪ β) (v : α →₀ M) : (embDomain f v).support = v.support.map f :=
  rfl

@[simp]
/-
**Finsupp.embDomain_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_zero (f : α ↪ β) : (embDomain f 0 : β ->₀ M) = 0
参数：f : α ↪ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem embDomain_zero (f : α ↪ β) : (embDomain f 0 : β →₀ M) = 0 :=
  rfl

open scoped Classical in
@[grind =]
/-
**Finsupp.embDomain_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_apply (f : α ↪ β) (v : α ->₀ M) (b : β) : embDomain f v b = if h
 : exists a, f a = b then v h.choose else 0
参数：f : α ↪ β；v : α ->₀ M；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem embDomain_apply (f : α ↪ β) (v : α →₀ M) (b : β) :
    embDomain f v b = if h : ∃ a, f a = b then v h.choose else 0 := by
  simp only [embDomain, coe_mk]
  -- TODO: investigate why `grind` needs `split_ifs` first; this should never happen.
  split_ifs <;> grind

@[simp, grind =]
/-
**Finsupp.embDomain_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_apply_self (f : α ↪ β) (v : α ->₀ M) (a : α) : embDomain f v (f 
a) = v a
参数：f : α ↪ β；v : α ->₀ M；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem embDomain_apply_self (f : α ↪ β) (v : α →₀ M) (a : α) : embDomain f v (f a) = v a := by
  simp_rw [embDomain, coe_mk]
  grind

@[grind =>]
/-
**Finsupp.embDomain_of_notMem_range** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_of_notMem_range (f : α ↪ β) (v : α ->₀ M) (a : β) (h : a ∉ Set.r
ange f) : embDomain f v a = 0
参数：f : α ↪ β；v : α ->₀ M；a : β；h : a ∉ Set.range f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem embDomain_of_notMem_range (f : α ↪ β) (v : α →₀ M) (a : β) (h : a ∉ Set.range f) :
    embDomain f v a = 0 := by grind [embDomain]

@[deprecated (since := "2026-07-15")] alias embDomain_notin_range := embDomain_of_notMem_range
/-
**Finsupp.embDomain_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_injective (f : α ↪ β) : Function.Injective (embDomain f : (α ->₀
 M) -> β ->₀ M)
参数：f : α ↪ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.embDomain_apply_self`：embDomain_apply_self (f : α ↪ β) (v : α ->
₀ M) (a : α) : embDomain f v (f a) = v a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem embDomain_injective (f : α ↪ β) : Function.Injective (embDomain f : (α →₀ M) → β →₀ M) :=
  fun l₁ l₂ h => ext fun a => by simpa only [embDomain_apply_self] using DFunLike.ext_iff.1 h (f a)

@[simp]
/-
**Finsupp.embDomain_inj** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_inj {f : α ↪ β} {l₁ l₂ : α ->₀ M} : embDomain f l₁ = embDomain f
 l₂ ↔ l₁ = l₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Finsupp.embDomain_injective`：embDomain_injective (f : α ↪ β) : Function.
Injective (embDomain f : (α ->₀ M) -> β ->₀ M)
-/
theorem embDomain_inj {f : α ↪ β} {l₁ l₂ : α →₀ M} : embDomain f l₁ = embDomain f l₂ ↔ l₁ = l₂ :=
  (embDomain_injective f).eq_iff

@[simp]
/-
**Finsupp.embDomain_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_eq_zero {f : α ↪ β} {l : α ->₀ M} : embDomain f l = 0 ↔ l = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Finsupp.embDomain_injective`：embDomain_injective (f : α ↪ β) : Function.
Injective (embDomain f : (α ->₀ M) -> β ->₀ M)
· 使用定理 `Finsupp.embDomain_zero`：embDomain_zero (f : α ↪ β) : (embDomain f 0 : β 
->₀ M) = 0
-/
theorem embDomain_eq_zero {f : α ↪ β} {l : α →₀ M} : embDomain f l = 0 ↔ l = 0 :=
  (embDomain_injective f).eq_iff' <| embDomain_zero f
/-
**Finsupp.embDomain_mapRange** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_mapRange (f : α ↪ β) (g : M -> N) (p : α ->₀ M) (hg : g 0 = 0) :
 embDomain f (mapRange g hg p) = mapRange g hg (embDomain f p)
参数：f : α ↪ β；g : M -> N；p : α ->₀ M；hg : g 0 = 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem embDomain_mapRange (f : α ↪ β) (g : M → N) (p : α →₀ M) (hg : g 0 = 0) :
    embDomain f (mapRange g hg p) = mapRange g hg (embDomain f p) := by grind

@[simp]
/-
**Finsupp.embDomain_refl** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_refl : embDomain (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.embDomain_apply`：embDomain_apply (f : α ↪ β) (v : α ->₀ M) (b : 
β) : embDomain f v b = if h : exists a, f a = b then v h.choose else 0
· 使用定理 `Function.Embedding.refl_apply`：∀ (α : Sort u_1) (a : α), (Function.Embed
ding.refl α) a = a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `Classical.choose_eq`：∀ {α : Sort u_1} (a : α), ⋯.choose = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma embDomain_refl : embDomain (M := M) (Function.Embedding.refl α) = id := by
  ext; simp [embDomain_apply]

end EmbDomain

/-! ### Declarations about `zipWith` -/


section ZipWith

variable [Zero M] [Zero N] [Zero O]

/-- Given finitely supported functions `g₁ : α →₀ M` and `g₂ : α →₀ N` and function `f : M → N → O`,
`Finsupp.zipWith f hf g₁ g₂` is the finitely supported function `α →₀ O` satisfying
`zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a)`, which is well-defined when `f 0 0 = 0`. -/
/-
**Finsupp.zipWith** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：zipWith (f : M -> N -> O) (hf : f 0 0 = 0) (g₁ : α ->₀ M) (g₂ : α ->₀ N) :
 α ->₀ O
参数：f : M -> N -> O；hf : f 0 0 = 0；g₁ : α ->₀ M；g₂ : α ->₀ N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given finitely supported functions `g₁ : α →₀ M` and `g₂ : α →₀ N` and function 
`f : M → N → O`,
`Finsupp.zipWith f hf g₁ g₂` is the finitely supported function `α →₀ O` satisfy
ing
`zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a)`, which is well-defined when `f 0 0 = 0`
.
-/
def zipWith (f : M → N → O) (hf : f 0 0 = 0) (g₁ : α →₀ M) (g₂ : α →₀ N) : α →₀ O :=
  onFinset
    (haveI := Classical.decEq α; g₁.support ∪ g₂.support)
    (fun a => f (g₁ a) (g₂ a))
    fun a (H : f _ _ ≠ 0) => by
      classical
      grind

@[simp, grind =]
/-
**Finsupp.zipWith_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：zipWith_apply {f : M -> N -> O} {hf : f 0 0 = 0} {g₁ : α ->₀ M} {g₂ : α ->
₀ N} {a : α} : zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipWith_apply {f : M → N → O} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} {a : α} :
    zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a) :=
  rfl
/-
**Finsupp.support_zipWith** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_zipWith [D : DecidableEq α] {f : M -> N -> O} {hf : f 0 0 = 0} {g₁
 : α ->₀ M} {g₂ : α ->₀ N} : (zipWith f hf g₁ g₂).support subseteq g₁.support un
ion g₂.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `Finsupp.support_onFinset_subset`：support_onFinset_subset {s : Finset α} 
{f : α -> M} {hf} : (onFinset s f hf).support subseteq s
-/
theorem support_zipWith [D : DecidableEq α] {f : M → N → O} {hf : f 0 0 = 0} {g₁ : α →₀ M}
    {g₂ : α →₀ N} : (zipWith f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support := by
  convert! support_onFinset_subset

end ZipWith

end Finsupp

