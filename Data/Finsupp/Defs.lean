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

/--
Definition of `Finsupp` / `Finsupp` 的定义

English:
structure Finsupp
  parameters: (α : Type*) (M : Type*) [Zero M]
  axioms and operations (3):
    - support : Finset α
    - toFun : α -> M
    - mem_support_toFun : forall a, a in support ↔ toFun a != 0

中文:
结构 Finsupp
  参数: (α : 类型) (M : 类型) [Zero M]
  公理与运算 (3 个):
    - support : Finset α
    - toFun : α -> M
    - mem_support_toFun : 对任意 a, a in support ↔ toFun a != 0
-/
structure Finsupp (α : Type*) (M : Type*) [Zero M] where
  /-- The support of a finitely supported function (aka `Finsupp`). -/
  support : Finset α
  /-- The underlying function of a bundled finitely supported function (aka `Finsupp`). -/
  toFun : α -> M
  /-- The witness that the support of a `Finsupp` is indeed the exact locus where its
  underlying function is nonzero. -/
  mem_support_toFun : forall a, a in support ↔ toFun a != 0

@[inherit_doc]
infixr:25 " ->₀ " => Finsupp

namespace Finsupp

/-! ### Basic declarations about `Finsupp` -/


section Basic

variable [Zero M]

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (α ->₀ M) α M
  body: ⟨toFun, by
    rintro ⟨s, f, hf⟩ ⟨t, g, hg⟩ (rfl : f = g)
    congr
    ext a
    exact (hf _).trans (hg _).symm⟩

initialize_simps_projections Finsupp (toFun -> apply)

@[ext, grind ext]

中文:
实例 instFunLike
  签名: : FunLike (α ->₀ M) α M
  定义体: ⟨toFun, by
    rintro ⟨s, f, hf⟩ ⟨t, g, hg⟩ (rfl : f = g)
    congr
    ext a
    exact (hf _).trans (hg _).symm⟩

initialize_simps_projections Finsupp (toFun -> apply)

@[ext, grind ext]
-/
instance instFunLike : FunLike (α ->₀ M) α M :=
  ⟨toFun, by
    rintro ⟨s, f, hf⟩ ⟨t, g, hg⟩ (rfl : f = g)
    congr
    ext a
    exact (hf _).trans (hg _).symm⟩

initialize_simps_projections Finsupp (toFun -> apply)

@[ext, grind ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : α ->₀ M} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {f g : α ->₀ M} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/--
Instance `instSubsingleton` / 实例 `instSubsingleton`

English:
instance instSubsingleton
  signature: [IsEmpty α]
  body: by ext x; exact isEmptyElim x

中文:
实例 instSubsingleton
  签名: [IsEmpty α]
  定义体: by ext x; exact isEmptyElim x

Depends on / 依赖: isEmptyElim
-/
instance instSubsingleton [IsEmpty α] : Subsingleton (α ->₀ M) where
  allEq f g := by ext x; exact isEmptyElim x

/--
Instance `instSubsingleton'` / 实例 `instSubsingleton'`

English:
instance instSubsingleton'
  signature: [Subsingleton M]
  body: by ext x; exact Subsingleton.elim ..

中文:
实例 instSubsingleton'
  签名: [Subsingleton M]
  定义体: by ext x; exact Subsingleton.elim ..

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
instance instSubsingleton' [Subsingleton M] : Subsingleton (α ->₀ M) where
  allEq f g := by ext x; exact Subsingleton.elim ..

variable (α) in
/--
theorem `nontrivial_of_nontrivial` / 定理 `nontrivial_of_nontrivial`

English:
theorem nontrivial_of_nontrivial
  given: [h : Nontrivial (α ->₀ M)]
  statement: Nontrivial M
  proof: by
  contrapose! h; infer_instance

中文:
定理 nontrivial_of_nontrivial
  条件: [h : Nontrivial (α ->₀ M)]
  结论: Nontrivial M
  证明: by
  contrapose! h; infer_instance

Depends on / 依赖: contrapose, infer_instance
-/
theorem nontrivial_of_nontrivial [h : Nontrivial (α ->₀ M)] : Nontrivial M := by
  contrapose! h; infer_instance

/--
lemma `ne_iff` / 引理 `ne_iff`

English:
lemma ne_iff
  given: {f g : α ->₀ M}
  statement: f != g ↔ exists a, f a != g a
  proof: DFunLike.ne_iff

@[simp, norm_cast, grind =]

中文:
引理 ne_iff
  条件: {f g : α ->₀ M}
  结论: f != g ↔ 存在 a, f a != g a
  证明: DFunLike.ne_iff

@[simp, norm_cast, grind =]

Depends on / 依赖: DFunLike, DFunLike.ne_iff, ne_iff
-/
lemma ne_iff {f g : α ->₀ M} : f != g ↔ exists a, f a != g a := DFunLike.ne_iff

@[simp, norm_cast, grind =]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : α -> M) (s : Finset α) (h : forall a, a in s ↔ f a != 0)
  statement: ⇑(⟨s, f, h⟩ : α ->₀ M) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : α -> M) (s : Finset α) (h : 对任意 a, a in s ↔ f a != 0)
  结论: ⇑(⟨s, f, h⟩ : α ->₀ M) = f
  证明: rfl
-/
theorem coe_mk (f : α -> M) (s : Finset α) (h : forall a, a in s ↔ f a != 0) : ⇑(⟨s, f, h⟩ : α ->₀ M) = f :=
  rfl

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (α ->₀ M)
  body: ⟨⟨∅, 0, fun _ => ⟨fun h => (notMem_empty _ h).elim, fun H => (H rfl).elim⟩⟩⟩

中文:
实例 instZero
  签名: : Zero (α ->₀ M)
  定义体: ⟨⟨∅, 0, fun _ => ⟨fun h => (notMem_empty _ h).elim, fun H => (H rfl).elim⟩⟩⟩

Depends on / 依赖: notMem_empty
-/
instance instZero : Zero (α ->₀ M) :=
  ⟨⟨∅, 0, fun _ => ⟨fun h => (notMem_empty _ h).elim, fun H => (H rfl).elim⟩⟩⟩

/--
lemma `coe_zero` / 引理 `coe_zero`

English:
lemma coe_zero
  statement: ⇑(0 : α ->₀ M) = 0
  proof: rfl

@[grind =]

中文:
引理 coe_zero
  结论: ⇑(0 : α ->₀ M) = 0
  证明: rfl

@[grind =]
-/
@[simp, norm_cast] lemma coe_zero : ⇑(0 : α ->₀ M) = 0 := rfl

@[grind =]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: {a : α}
  statement: (0 : α ->₀ M) a = 0
  proof: rfl

@[simp, grind =]

中文:
定理 zero_apply
  条件: {a : α}
  结论: (0 : α ->₀ M) a = 0
  证明: rfl

@[simp, grind =]
-/
theorem zero_apply {a : α} : (0 : α ->₀ M) a = 0 :=
  rfl

@[simp, grind =]
/--
theorem `support_zero` / 定理 `support_zero`

English:
theorem support_zero
  statement: (0 : α ->₀ M).support = ∅
  proof: rfl

中文:
定理 support_zero
  结论: (0 : α ->₀ M).support = ∅
  证明: rfl
-/
theorem support_zero : (0 : α ->₀ M).support = ∅ :=
  rfl

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (α ->₀ M)
  body: ⟨0⟩

中文:
实例 instInhabited
  签名: : Inhabited (α ->₀ M)
  定义体: ⟨0⟩
-/
instance instInhabited : Inhabited (α ->₀ M) :=
  ⟨0⟩

/--
lemma `default_eq_zero` / 引理 `default_eq_zero`

English:
lemma default_eq_zero
  statement: (default : α ->₀ M) = 0
  proof: rfl

@[simp, grind =]

中文:
引理 default_eq_zero
  结论: (default : α ->₀ M) = 0
  证明: rfl

@[simp, grind =]
-/
@[simp] lemma default_eq_zero : (default : α ->₀ M) = 0 := rfl

@[simp, grind =]
/--
theorem `mem_support_iff` / 定理 `mem_support_iff`

English:
theorem mem_support_iff
  given: {f : α ->₀ M}
  statement: forall {a : α}, a in f.support ↔ f a != 0
  proof: @(f.mem_support_toFun)

@[simp, norm_cast]

中文:
定理 mem_support_iff
  条件: {f : α ->₀ M}
  结论: 对任意 {a : α}, a in f.support ↔ f a != 0
  证明: @(f.mem_support_toFun)

@[simp, norm_cast]

Depends on / 依赖: f.mem_support_toFun, mem_support_toFun
-/
theorem mem_support_iff {f : α ->₀ M} : forall {a : α}, a in f.support ↔ f a != 0 :=
  @(f.mem_support_toFun)

@[simp, norm_cast]
/--
theorem `fun_support_eq` / 定理 `fun_support_eq`

English:
theorem fun_support_eq
  given: (f : α ->₀ M)
  statement: Function.support f = f.support
  proof: Set.ext fun _x => mem_support_iff.symm

中文:
定理 fun_support_eq
  条件: (f : α ->₀ M)
  结论: Function.support f = f.support
  证明: Set.ext fun _x => mem_support_iff.symm

Depends on / 依赖: Set.ext, mem_support_iff, mem_support_iff.symm
-/
theorem fun_support_eq (f : α ->₀ M) : Function.support f = f.support :=
  Set.ext fun _x => mem_support_iff.symm

/--
theorem `notMem_support_iff` / 定理 `notMem_support_iff`

English:
theorem notMem_support_iff
  given: {f : α ->₀ M} {a}
  statement: a ∉ f.support ↔ f a = 0
  proof: not_iff_comm.1 mem_support_iff.symm

@[simp, norm_cast]

中文:
定理 notMem_support_iff
  条件: {f : α ->₀ M} {a}
  结论: a ∉ f.support ↔ f a = 0
  证明: not_iff_comm.1 mem_support_iff.symm

@[simp, norm_cast]

Depends on / 依赖: Nat.Prime.one_lt, mem_support_iff, mem_support_iff.symm, not_iff_comm, one_lt
-/
theorem notMem_support_iff {f : α ->₀ M} {a} : a ∉ f.support ↔ f a = 0 :=
  not_iff_comm.1 mem_support_iff.symm

@[simp, norm_cast]
/--
theorem `coe_eq_zero` / 定理 `coe_eq_zero`

English:
theorem coe_eq_zero
  given: {f : α ->₀ M}
  statement: (f : α -> M) = 0 ↔ f = 0
  proof: by rw [← coe_zero, DFunLike.coe_fn_eq]

中文:
定理 coe_eq_zero
  条件: {f : α ->₀ M}
  结论: (f : α -> M) = 0 ↔ f = 0
  证明: by rw [← coe_zero, DFunLike.coe_fn_eq]

Depends on / 依赖: DFunLike, DFunLike.coe_fn_eq, coe_fn_eq, coe_zero
-/
theorem coe_eq_zero {f : α ->₀ M} : (f : α -> M) = 0 ↔ f = 0 := by rw [← coe_zero, DFunLike.coe_fn_eq]

/--
theorem `ext_iff'` / 定理 `ext_iff'`

English:
theorem ext_iff'
  given: {f g : α ->₀ M}
  statement: f = g ↔ f.support = g.support ∧ forall x in f.support, f x = g x
  proof: ⟨fun h => h ▸ ⟨rfl, fun _ _ => rfl⟩, fun ⟨h₁, h₂⟩ =>
    ext fun a => by
      classical
      exact if h : a in f.support then h₂ a h else by
        have hf : f a = 0 := notMem_support_iff.1 h
        have hg : g a = 0 := by rwa [h₁, notMem_support_iff] at h
        rw [hf]; rw [hg]⟩

@[simp]

中文:
定理 ext_iff'
  条件: {f g : α ->₀ M}
  结论: f = g ↔ f.support = g.support ∧ 对任意 x in f.support, f x = g x
  证明: ⟨fun h => h ▸ ⟨rfl, fun _ _ => rfl⟩, fun ⟨h₁, h₂⟩ =>
    ext fun a => by
      classical
      exact if h : a in f.support then h₂ a h else by
        have hf : f a = 0 := notMem_support_iff.1 h
        have hg : g a = 0 := by rwa [h₁, notMem_support_iff] at h
        rw [hf]; rw [hg]⟩

@[simp]

Depends on / 依赖: classical, f.support, notMem_support_iff, support
-/
theorem ext_iff' {f g : α ->₀ M} : f = g ↔ f.support = g.support ∧ forall x in f.support, f x = g x :=
  ⟨fun h => h ▸ ⟨rfl, fun _ _ => rfl⟩, fun ⟨h₁, h₂⟩ =>
    ext fun a => by
      classical
      exact if h : a in f.support then h₂ a h else by
        have hf : f a = 0 := notMem_support_iff.1 h
        have hg : g a = 0 := by rwa [h₁, notMem_support_iff] at h
        rw [hf]; rw [hg]⟩

@[simp]
/--
theorem `support_eq_empty` / 定理 `support_eq_empty`

English:
theorem support_eq_empty
  given: {f : α ->₀ M}
  statement: f.support = ∅ ↔ f = 0
  proof: mod_cast @Function.support_eq_empty_iff _ _ _ f

@[simp]

中文:
定理 support_eq_empty
  条件: {f : α ->₀ M}
  结论: f.support = ∅ ↔ f = 0
  证明: mod_cast @Function.support_eq_empty_iff _ _ _ f

@[simp]

Depends on / 依赖: Function, Function.support_eq_empty_iff, mod_cast, support_eq_empty_iff
-/
theorem support_eq_empty {f : α ->₀ M} : f.support = ∅ ↔ f = 0 :=
  mod_cast @Function.support_eq_empty_iff _ _ _ f

@[simp]
/--
theorem `support_nonempty_iff` / 定理 `support_nonempty_iff`

English:
theorem support_nonempty_iff
  given: {f : α ->₀ M}
  statement: f.support.Nonempty ↔ f != 0
  proof: by
  contrapose!; exact support_eq_empty

中文:
定理 support_nonempty_iff
  条件: {f : α ->₀ M}
  结论: f.support.Nonempty ↔ f != 0
  证明: by
  contrapose!; exact support_eq_empty

Depends on / 依赖: contrapose, support_eq_empty
-/
theorem support_nonempty_iff {f : α ->₀ M} : f.support.Nonempty ↔ f != 0 := by
  contrapose!; exact support_eq_empty

/--
theorem `card_support_eq_zero` / 定理 `card_support_eq_zero`

English:
theorem card_support_eq_zero
  given: {f : α ->₀ M}
  statement: #f.support = 0 ↔ f = 0
  proof: by simp

中文:
定理 card_support_eq_zero
  条件: {f : α ->₀ M}
  结论: #f.support = 0 ↔ f = 0
  证明: by simp
-/
theorem card_support_eq_zero {f : α ->₀ M} : #f.support = 0 ↔ f = 0 := by simp

/--
Instance `instDecidableEq` / 实例 `instDecidableEq`

English:
instance instDecidableEq
  signature: [DecidableEq α] [DecidableEq M]
  body: fun f g =>
  decidable_of_iff (f.support = g.support ∧ forall a in f.support, f a = g a) ext_iff'.symm

@[fun_prop]

中文:
实例 instDecidableEq
  签名: [DecidableEq α] [DecidableEq M]
  定义体: fun f g =>
  decidable_of_iff (f.support = g.support ∧ forall a in f.support, f a = g a) ext_iff'.symm

@[fun_prop]
-/
instance instDecidableEq [DecidableEq α] [DecidableEq M] : DecidableEq (α ->₀ M) := fun f g =>
  decidable_of_iff (f.support = g.support ∧ forall a in f.support, f a = g a) ext_iff'.symm

@[fun_prop]
/--
theorem `hasFiniteSupport` / 定理 `hasFiniteSupport`

English:
theorem hasFiniteSupport
  given: (f : α ->₀ M)
  statement: HasFiniteSupport f
  proof: by
  rw [HasFiniteSupport]
  exact f.fun_support_eq.symm ▸ f.support.finite_toSet

@[deprecated (since := "2026-03-03")] alias finite_support := hasFiniteSupport

中文:
定理 hasFiniteSupport
  条件: (f : α ->₀ M)
  结论: HasFiniteSupport f
  证明: by
  rw [HasFiniteSupport]
  exact f.fun_support_eq.symm ▸ f.support.finite_toSet

@[deprecated (since := "2026-03-03")] alias finite_support := hasFiniteSupport

Depends on / 依赖: HasFiniteSupport, f.fun_support_eq.symm, f.support.finite_toSet, finite_toSet, fun_support_eq, support
-/
theorem hasFiniteSupport (f : α ->₀ M) : HasFiniteSupport f := by
  rw [HasFiniteSupport]
  exact f.fun_support_eq.symm ▸ f.support.finite_toSet

@[deprecated (since := "2026-03-03")] alias finite_support := hasFiniteSupport

/--
theorem `support_subset_iff` / 定理 `support_subset_iff`

English:
theorem support_subset_iff
  given: {s : Set α} {f : α ->₀ M}
  proof: by
  grind

中文:
定理 support_subset_iff
  条件: {s : Set α} {f : α ->₀ M}
  证明: by
  grind
-/
theorem support_subset_iff {s : Set α} {f : α ->₀ M} :
    ↑f.support subseteq s ↔ forall a ∉ s, f a = 0 := by
  grind

/-- Given `Finite α`, `equivFunOnFinite` is the `Equiv` between `α →₀ β` and `α → β`.
  (All functions on a finite type are finitely supported.) -/
@[simps]
/--
Definition of `equivFunOnFinite` / `equivFunOnFinite` 的定义

English:
definition equivFunOnFinite
  signature: [Finite α]
  body: (⇑)
  invFun f := mk (Function.support f).toFinite.toFinset f fun _a => Set.Finite.mem_toFinset _

@[simp]

中文:
定义 equivFunOnFinite
  签名: [Finite α]
  定义体: (⇑)
  invFun f := mk (Function.support f).toFinite.toFinset f fun _a => Set.Finite.mem_toFinset _

@[simp]

Depends on / 依赖: Nat.Prime.ne_one, PNat.coe_eq_one_iff, coe_eq_one_iff, contra, ne_one
-/
def equivFunOnFinite [Finite α] : (α ->₀ M) ≃ (α -> M) where
  toFun := (⇑)
  invFun f := mk (Function.support f).toFinite.toFinset f fun _a => Set.Finite.mem_toFinset _

@[simp]
/--
theorem `equivFunOnFinite_symm_coe` / 定理 `equivFunOnFinite_symm_coe`

English:
theorem equivFunOnFinite_symm_coe
  given: {α} [Finite α] (f : α ->₀ M)
  statement: equivFunOnFinite.symm f = f
  proof: equivFunOnFinite.symm_apply_apply f

@[simp]

中文:
定理 equivFunOnFinite_symm_coe
  条件: {α} [Finite α] (f : α ->₀ M)
  结论: equivFunOnFinite.symm f = f
  证明: equivFunOnFinite.symm_apply_apply f

@[simp]

Depends on / 依赖: equivFunOnFinite, equivFunOnFinite.symm_apply_apply, symm_apply_apply
-/
theorem equivFunOnFinite_symm_coe {α} [Finite α] (f : α ->₀ M) : equivFunOnFinite.symm f = f :=
  equivFunOnFinite.symm_apply_apply f

@[simp]
/--
lemma `coe_equivFunOnFinite_symm` / 引理 `coe_equivFunOnFinite_symm`

English:
lemma coe_equivFunOnFinite_symm
  given: {α} [Finite α] (f : α -> M)
  statement: ⇑(equivFunOnFinite.symm f) = f
  proof: rfl

@[ext]

中文:
引理 coe_equivFunOnFinite_symm
  条件: {α} [Finite α] (f : α -> M)
  结论: ⇑(equivFunOnFinite.symm f) = f
  证明: rfl

@[ext]

Depends on / 依赖: Nat.Prime.not_dvd_one, dvd_iff, not_dvd_one, p.Prime
-/
lemma coe_equivFunOnFinite_symm {α} [Finite α] (f : α -> M) : ⇑(equivFunOnFinite.symm f) = f := rfl

@[ext]
/--
theorem `unique_ext` / 定理 `unique_ext`

English:
theorem unique_ext
  given: [Unique α] {f g : α ->₀ M} (h : f default = g default)
  statement: f = g
  proof: ext fun a => by rwa [Unique.eq_default a]

中文:
定理 unique_ext
  条件: [Unique α] {f g : α ->₀ M} (h : f default = g default)
  结论: f = g
  证明: ext fun a => by rwa [Unique.eq_default a]

Depends on / 依赖: Unique, Unique.eq_default, eq_default
-/
theorem unique_ext [Unique α] {f g : α ->₀ M} (h : f default = g default) : f = g :=
  ext fun a => by rwa [Unique.eq_default a]

end Basic

/-! ### Declarations about `onFinset` -/


section OnFinset

variable [Zero M]

/--
Definition of `onFinsetSupport` / `onFinsetSupport` 的定义

English:
definition onFinsetSupport
  signature: (s : Finset α) (f : α -> M)
  body: haveI := Classical.decEq M
  {a in s | f a != 0}

中文:
定义 onFinsetSupport
  签名: (s : Finset α) (f : α -> M)
  定义体: haveI := Classical.decEq M
  {a in s | f a != 0}
-/
@[no_expose] def onFinsetSupport (s : Finset α) (f : α -> M) : Finset α :=
  haveI := Classical.decEq M
  {a in s | f a != 0}

/--
Definition of `onFinset` / `onFinset` 的定义

English:
definition onFinset
  signature: (s : Finset α) (f : α -> M) (hf : forall a, f a != 0 -> a in s)
  body: onFinsetSupport s f
  toFun := f
  mem_support_toFun := by simpa [onFinsetSupport]

中文:
定义 onFinset
  签名: (s : Finset α) (f : α -> M) (hf : 对任意 a, f a != 0 -> a in s)
  定义体: onFinsetSupport s f
  toFun := f
  mem_support_toFun := by simpa [onFinsetSupport]

Depends on / 依赖: onFinsetSupport
-/
def onFinset (s : Finset α) (f : α -> M) (hf : forall a, f a != 0 -> a in s) : α ->₀ M where
  support := onFinsetSupport s f
  toFun := f
  mem_support_toFun := by simpa [onFinsetSupport]

/--
lemma `coe_onFinset` / 引理 `coe_onFinset`

English:
lemma coe_onFinset
  given: (s : Finset α) (f : α -> M) (hf)
  statement: onFinset s f hf = f
  proof: rfl

@[simp, grind =]

中文:
引理 coe_onFinset
  条件: (s : Finset α) (f : α -> M) (hf)
  结论: onFinset s f hf = f
  证明: rfl

@[simp, grind =]
-/
@[simp, norm_cast] lemma coe_onFinset (s : Finset α) (f : α -> M) (hf) : onFinset s f hf = f := rfl

@[simp, grind =]
/--
theorem `onFinset_apply` / 定理 `onFinset_apply`

English:
theorem onFinset_apply
  given: {s : Finset α} {f : α -> M} {hf a}
  statement: (onFinset s f hf : α ->₀ M) a = f a
  proof: rfl

中文:
定理 onFinset_apply
  条件: {s : Finset α} {f : α -> M} {hf a}
  结论: (onFinset s f hf : α ->₀ M) a = f a
  证明: rfl
-/
theorem onFinset_apply {s : Finset α} {f : α -> M} {hf a} : (onFinset s f hf : α ->₀ M) a = f a :=
  rfl

/--
theorem `support_onFinset` / 定理 `support_onFinset`

English:
theorem support_onFinset
  statement: [DecidableEq M] {s : Finset α} {f : α -> M}
  proof: by
  dsimp [onFinset]; rw [onFinsetSupport]; congr

中文:
定理 support_onFinset
  结论: [DecidableEq M] {s : Finset α} {f : α -> M}
  证明: by
  dsimp [onFinset]; rw [onFinsetSupport]; congr

Depends on / 依赖: onFinset, onFinsetSupport
-/
theorem support_onFinset [DecidableEq M] {s : Finset α} {f : α -> M}
    (hf : forall a : α, f a != 0 -> a in s) :
    (Finsupp.onFinset s f hf).support = {a in s | f a != 0} := by
  dsimp [onFinset]; rw [onFinsetSupport]; congr

/--
lemma `onFinset_support` / 引理 `onFinset_support`

English:
lemma onFinset_support
  given: (f : α ->₀ M)
  statement: onFinset f.support f (by simp) = f
  proof: by ext; simp

@[simp]

中文:
引理 onFinset_support
  条件: (f : α ->₀ M)
  结论: onFinset f.support f (by simp) = f
  证明: by ext; simp

@[simp]
-/
@[simp] lemma onFinset_support (f : α ->₀ M) : onFinset f.support f (by simp) = f := by ext; simp

@[simp]
/--
theorem `support_onFinset_subset` / 定理 `support_onFinset_subset`

English:
theorem support_onFinset_subset
  given: {s : Finset α} {f : α -> M} {hf}
  proof: by
  grind

grind_pattern support_onFinset_subset => onFinset s f hf

中文:
定理 support_onFinset_subset
  条件: {s : Finset α} {f : α -> M} {hf}
  证明: by
  grind

grind_pattern support_onFinset_subset => onFinset s f hf
-/
theorem support_onFinset_subset {s : Finset α} {f : α -> M} {hf} :
    (onFinset s f hf).support subseteq s := by
  grind

grind_pattern support_onFinset_subset => onFinset s f hf

/--
theorem `mem_support_onFinset` / 定理 `mem_support_onFinset`

English:
theorem mem_support_onFinset
  given: {s : Finset α} {f : α -> M} (hf : forall a : α, f a != 0 -> a in s) {a : α}
  proof: by
  rw [Finsupp.mem_support_iff]; rw [Finsupp.onFinset_apply]

中文:
定理 mem_support_onFinset
  条件: {s : Finset α} {f : α -> M} (hf : 对任意 a : α, f a != 0 -> a in s) {a : α}
  证明: by
  rw [Finsupp.mem_support_iff]; rw [Finsupp.onFinset_apply]

Depends on / 依赖: Finsupp, Finsupp.mem_support_iff, Finsupp.onFinset_apply, mem_support_iff, onFinset_apply
-/
theorem mem_support_onFinset {s : Finset α} {f : α -> M} (hf : forall a : α, f a != 0 -> a in s) {a : α} :
    a in (Finsupp.onFinset s f hf).support ↔ f a != 0 := by
  rw [Finsupp.mem_support_iff]; rw [Finsupp.onFinset_apply]

end OnFinset

section OfSupportFinite

variable [Zero M]

/--
Definition of `ofSupportFinite` / `ofSupportFinite` 的定义

English:
definition ofSupportFinite
  signature: (f : α -> M) (hf : (Function.support f).Finite)
  body: hf.toFinset
  toFun := f
  mem_support_toFun _ := hf.mem_toFinset

中文:
定义 ofSupportFinite
  签名: (f : α -> M) (hf : (Function.support f).Finite)
  定义体: hf.toFinset
  toFun := f
  mem_support_toFun _ := hf.mem_toFinset

Depends on / 依赖: hf.toFinset, toFinset
-/
noncomputable def ofSupportFinite (f : α -> M) (hf : (Function.support f).Finite) : α ->₀ M where
  support := hf.toFinset
  toFun := f
  mem_support_toFun _ := hf.mem_toFinset

/--
theorem `ofSupportFinite_coe` / 定理 `ofSupportFinite_coe`

English:
theorem ofSupportFinite_coe
  given: {f : α -> M} {hf : (Function.support f).Finite}
  proof: rfl

中文:
定理 ofSupportFinite_coe
  条件: {f : α -> M} {hf : (Function.support f).Finite}
  证明: rfl
-/
theorem ofSupportFinite_coe {f : α -> M} {hf : (Function.support f).Finite} :
    (ofSupportFinite f hf : α -> M) = f :=
  rfl

/--
theorem `ofSupportFinite_support` / 定理 `ofSupportFinite_support`

English:
theorem ofSupportFinite_support
  given: {f : α -> M} (hf : f.support.Finite)
  proof: by
  ext; simp [ofSupportFinite_coe]

中文:
定理 ofSupportFinite_support
  条件: {f : α -> M} (hf : f.support.Finite)
  证明: by
  ext; simp [ofSupportFinite_coe]

Depends on / 依赖: ofSupportFinite_coe
-/
theorem ofSupportFinite_support {f : α -> M} (hf : f.support.Finite) :
    (ofSupportFinite f hf).support = hf.toFinset := by
  ext; simp [ofSupportFinite_coe]

/--
Instance `instCanLift` / 实例 `instCanLift`

English:
instance instCanLift
  signature: : CanLift (α -> M) (α ->₀ M) (⇑) fun f => (Function.support f).Finite where
  body: ⟨ofSupportFinite f hf, rfl⟩

中文:
实例 instCanLift
  签名: : CanLift (α -> M) (α ->₀ M) (⇑) fun f => (Function.support f).Finite where
  定义体: ⟨ofSupportFinite f hf, rfl⟩

Depends on / 依赖: ofSupportFinite
-/
instance instCanLift : CanLift (α -> M) (α ->₀ M) (⇑) fun f => (Function.support f).Finite where
  prf f hf := ⟨ofSupportFinite f hf, rfl⟩

end OfSupportFinite

/-! ### Declarations about `mapRange` -/


section MapRange

variable [Zero M] [Zero N] [Zero O]

/--
Definition of `mapRange` / `mapRange` 的定义

English:
definition mapRange
  signature: (f : M -> N) (hf : f 0 = 0) (g : α ->₀ M)
  body: onFinset g.support (f ∘ g) fun a => by
    rw [mem_support_iff]; rw [not_imp_not]; exact fun H => (congr_arg f H).trans hf

@[simp, grind =]

中文:
定义 mapRange
  签名: (f : M -> N) (hf : f 0 = 0) (g : α ->₀ M)
  定义体: onFinset g.support (f ∘ g) fun a => by
    rw [mem_support_iff]; rw [not_imp_not]; exact fun H => (congr_arg f H).trans hf

@[simp, grind =]

Depends on / 依赖: congr_arg, g.support, mem_support_iff, not_imp_not, onFinset, support
-/
def mapRange (f : M -> N) (hf : f 0 = 0) (g : α ->₀ M) : α ->₀ N :=
  onFinset g.support (f ∘ g) fun a => by
    rw [mem_support_iff]; rw [not_imp_not]; exact fun H => (congr_arg f H).trans hf

@[simp, grind =]
/--
theorem `mapRange_apply` / 定理 `mapRange_apply`

English:
theorem mapRange_apply
  given: {f : M -> N} {hf : f 0 = 0} {g : α ->₀ M} {a : α}
  proof: rfl

@[simp]

中文:
定理 mapRange_apply
  条件: {f : M -> N} {hf : f 0 = 0} {g : α ->₀ M} {a : α}
  证明: rfl

@[simp]
-/
theorem mapRange_apply {f : M -> N} {hf : f 0 = 0} {g : α ->₀ M} {a : α} :
    mapRange f hf g a = f (g a) :=
  rfl

@[simp]
/--
theorem `mapRange_zero` / 定理 `mapRange_zero`

English:
theorem mapRange_zero
  given: {f : M -> N} {hf : f 0 = 0}
  statement: mapRange f hf (0 : α ->₀ M) = 0
  proof: ext fun _ => by simp only [hf, zero_apply, mapRange_apply]

@[simp]

中文:
定理 mapRange_zero
  条件: {f : M -> N} {hf : f 0 = 0}
  结论: mapRange f hf (0 : α ->₀ M) = 0
  证明: ext fun _ => by simp only [hf, zero_apply, mapRange_apply]

@[simp]

Depends on / 依赖: mapRange_apply, zero_apply
-/
theorem mapRange_zero {f : M -> N} {hf : f 0 = 0} : mapRange f hf (0 : α ->₀ M) = 0 :=
  ext fun _ => by simp only [hf, zero_apply, mapRange_apply]

@[simp]
/--
theorem `mapRange_eq_zero` / 定理 `mapRange_eq_zero`

English:
theorem mapRange_eq_zero
  given: {a : α ->₀ M} {f : M -> N} (hf : f.Injective) (h)
  proof: by
  simp [Finsupp.ext_iff, ← h, hf.eq_iff]

@[simp]

中文:
定理 mapRange_eq_zero
  条件: {a : α ->₀ M} {f : M -> N} (hf : f.Injective) (h)
  证明: by
  simp [Finsupp.ext_iff, ← h, hf.eq_iff]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.ext_iff, eq_iff, ext_iff, hf.eq_iff
-/
theorem mapRange_eq_zero {a : α ->₀ M} {f : M -> N} (hf : f.Injective) (h) :
    mapRange f h a = 0 ↔ a = 0 := by
  simp [Finsupp.ext_iff, ← h, hf.eq_iff]

@[simp]
/--
theorem `mapRange_id` / 定理 `mapRange_id`

English:
theorem mapRange_id
  given: (g : α ->₀ M)
  statement: mapRange id rfl g = g
  proof: ext fun _ => rfl

中文:
定理 mapRange_id
  条件: (g : α ->₀ M)
  结论: mapRange id rfl g = g
  证明: ext fun _ => rfl
-/
theorem mapRange_id (g : α ->₀ M) : mapRange id rfl g = g :=
  ext fun _ => rfl

/--
theorem `mapRange_comp` / 定理 `mapRange_comp`

English:
theorem mapRange_comp
  statement: (f : N -> O) (hf : f 0 = 0) (f₂ : M -> N) (hf₂ : f₂ 0 = 0) (h : (f ∘ f₂) 0 = 0)
  proof: ext fun _ => rfl

@[simp]

中文:
定理 mapRange_comp
  结论: (f : N -> O) (hf : f 0 = 0) (f₂ : M -> N) (hf₂ : f₂ 0 = 0) (h : (f ∘ f₂) 0 = 0)
  证明: ext fun _ => rfl

@[simp]
-/
theorem mapRange_comp (f : N -> O) (hf : f 0 = 0) (f₂ : M -> N) (hf₂ : f₂ 0 = 0) (h : (f ∘ f₂) 0 = 0)
    (g : α ->₀ M) : mapRange (f ∘ f₂) h g = mapRange f hf (mapRange f₂ hf₂ g) :=
  ext fun _ => rfl

@[simp]
/--
lemma `mapRange_mapRange` / 引理 `mapRange_mapRange`

English:
lemma mapRange_mapRange
  given: (e₁ : N -> O) (e₂ : M -> N) (he₁ he₂) (f : α ->₀ M)
  proof: ext fun _ => rfl

中文:
引理 mapRange_mapRange
  条件: (e₁ : N -> O) (e₂ : M -> N) (he₁ he₂) (f : α ->₀ M)
  证明: ext fun _ => rfl
-/
lemma mapRange_mapRange (e₁ : N -> O) (e₂ : M -> N) (he₁ he₂) (f : α ->₀ M) :
    mapRange e₁ he₁ (mapRange e₂ he₂ f) = mapRange (e₁ ∘ e₂) (by simp [*]) f := ext fun _ => rfl

/--
theorem `support_mapRange` / 定理 `support_mapRange`

English:
theorem support_mapRange
  given: {f : M -> N} {hf : f 0 = 0} {g : α ->₀ M}
  proof: support_onFinset_subset

中文:
定理 support_mapRange
  条件: {f : M -> N} {hf : f 0 = 0} {g : α ->₀ M}
  证明: support_onFinset_subset

Depends on / 依赖: support_onFinset_subset
-/
theorem support_mapRange {f : M -> N} {hf : f 0 = 0} {g : α ->₀ M} :
    (mapRange f hf g).support subseteq g.support :=
  support_onFinset_subset

/--
theorem `support_mapRange_of_injective` / 定理 `support_mapRange_of_injective`

English:
theorem support_mapRange_of_injective
  statement: {e : M -> N} (he0 : e 0 = 0) (f : ι ->₀ M)
  proof: by grind

中文:
定理 support_mapRange_of_injective
  结论: {e : M -> N} (he0 : e 0 = 0) (f : ι ->₀ M)
  证明: by grind
-/
theorem support_mapRange_of_injective {e : M -> N} (he0 : e 0 = 0) (f : ι ->₀ M)
    (he : Function.Injective e) : (Finsupp.mapRange e he0 f).support = f.support := by grind

/--
lemma `range_mapRange` / 引理 `range_mapRange`

English:
lemma range_mapRange
  given: (e : M -> N) (he₀ : e 0 = 0)
  proof: by
  ext g
  simp only [Set.mem_range, Set.mem_ofPred]
  constructor
  · grind
  · intro h
    classical
    choose f h using h
    use onFinset g.support (fun x => if x in g.support then f x else 0) (by simp_all)
    grind

中文:
引理 range_mapRange
  条件: (e : M -> N) (he₀ : e 0 = 0)
  证明: by
  ext g
  simp only [Set.mem_range, Set.mem_ofPred]
  constructor
  · grind
  · intro h
    classical
    choose f h using h
    use onFinset g.support (fun x => if x in g.support then f x else 0) (by simp_all)
    grind

Depends on / 依赖: Set.mem_ofPred, Set.mem_range, Set.range, classical, g.support, mem_ofPred, mem_range, onFinset, support
-/
lemma range_mapRange (e : M -> N) (he₀ : e 0 = 0) :
    Set.range (Finsupp.mapRange (α := α) e he₀) = {g | forall i, g i in Set.range e} := by
  ext g
  simp only [Set.mem_range, Set.mem_ofPred]
  constructor
  · grind
  · intro h
    classical
    choose f h using h
    use onFinset g.support (fun x => if x in g.support then f x else 0) (by simp_all)
    grind

/--
lemma `mapRange_injective` / 引理 `mapRange_injective`

English:
lemma mapRange_injective
  given: (e : M -> N) (he₀ : e 0 = 0) (he : Injective e)
  proof: by
  intro a b h
  rw [Finsupp.ext_iff] at h ⊢
  simpa only [mapRange_apply, he.eq_iff] using h

中文:
引理 mapRange_injective
  条件: (e : M -> N) (he₀ : e 0 = 0) (he : Injective e)
  证明: by
  intro a b h
  rw [Finsupp.ext_iff] at h ⊢
  simpa only [mapRange_apply, he.eq_iff] using h

Depends on / 依赖: Finsupp, Finsupp.ext_iff, eq_iff, ext_iff, he.eq_iff, mapRange_apply
-/
lemma mapRange_injective (e : M -> N) (he₀ : e 0 = 0) (he : Injective e) :
    Injective (Finsupp.mapRange (α := α) e he₀) := by
  intro a b h
  rw [Finsupp.ext_iff] at h ⊢
  simpa only [mapRange_apply, he.eq_iff] using h

/--
lemma `mapRange_surjective` / 引理 `mapRange_surjective`

English:
lemma mapRange_surjective
  given: (e : M -> N) (he₀ : e 0 = 0) (he : Surjective e)
  proof: by
  rw [← Set.range_eq_univ]; rw [range_mapRange]; rw [he.range_eq]
  simp

中文:
引理 mapRange_surjective
  条件: (e : M -> N) (he₀ : e 0 = 0) (he : Surjective e)
  证明: by
  rw [← Set.range_eq_univ]; rw [range_mapRange]; rw [he.range_eq]
  simp

Depends on / 依赖: Set.range_eq_univ, he.range_eq, range_eq, range_eq_univ, range_mapRange
-/
lemma mapRange_surjective (e : M -> N) (he₀ : e 0 = 0) (he : Surjective e) :
    Surjective (Finsupp.mapRange (α := α) e he₀) := by
  rw [← Set.range_eq_univ]; rw [range_mapRange]; rw [he.range_eq]
  simp

/--
lemma `mapRange_bijective` / 引理 `mapRange_bijective`

English:
lemma mapRange_bijective
  given: (e : M -> N) (he₀ : e 0 = 0) (he : Bijective e)
  proof: ⟨mapRange_injective e he₀ he.1, mapRange_surjective e he₀ he.2⟩

中文:
引理 mapRange_bijective
  条件: (e : M -> N) (he₀ : e 0 = 0) (he : Bijective e)
  证明: ⟨mapRange_injective e he₀ he.1, mapRange_surjective e he₀ he.2⟩
-/
lemma mapRange_bijective (e : M -> N) (he₀ : e 0 = 0) (he : Bijective e) :
    Bijective (Finsupp.mapRange (α := α) e he₀) :=
  ⟨mapRange_injective e he₀ he.1, mapRange_surjective e he₀ he.2⟩

end MapRange

section Equiv
variable [Zero M] [Zero N] [Zero O]

/-- `Finsupp.mapRange` as an equiv. -/
@[simps (attr := grind =) apply]
/--
Definition of `mapRange.equiv` / `mapRange.equiv` 的定义

English:
definition mapRange.equiv
  signature: (e : M ≃ N) (hf : e 0 = 0)
  body: mapRange e hf
invFun := mapRange e.symm by simp [← hf]
  left_inv x := by ext; simp
  right_inv x := by ext; simp

中文:
定义 mapRange.equiv
  签名: (e : M ≃ N) (hf : e 0 = 0)
  定义体: mapRange e hf
invFun := mapRange e.symm by simp [← hf]
  left_inv x := by ext; simp
  right_inv x := by ext; simp

Depends on / 依赖: mapRange
-/
def mapRange.equiv (e : M ≃ N) (hf : e 0 = 0) : (ι ->₀ M) ≃ (ι ->₀ N) where
  toFun := mapRange e hf
invFun := mapRange e.symm by simp [← hf]
  left_inv x := by ext; simp
  right_inv x := by ext; simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mapRange.equiv_refl` / 引理 `mapRange.equiv_refl`

English:
lemma mapRange.equiv_refl
  statement: mapRange.equiv (.refl M) rfl = .refl (ι ->₀ M)
  proof: by ext; simp

中文:
引理 mapRange.equiv_refl
  结论: mapRange.equiv (.refl M) rfl = .refl (ι ->₀ M)
  证明: by ext; simp
-/
@[simp] lemma mapRange.equiv_refl : mapRange.equiv (.refl M) rfl = .refl (ι ->₀ M) := by ext; simp

/--
lemma `mapRange.equiv_trans` / 引理 `mapRange.equiv_trans`

English:
lemma mapRange.equiv_trans
  given: (e : M ≃ N) (hf) (f₂ : N ≃ O) (hf₂)
  proof: by ext; simp

@[simp, grind =]

中文:
引理 mapRange.equiv_trans
  条件: (e : M ≃ N) (hf) (f₂ : N ≃ O) (hf₂)
  证明: by ext; simp

@[simp, grind =]

Depends on / 依赖: Equiv.trans_apply, e.trans, trans_apply
-/
lemma mapRange.equiv_trans (e : M ≃ N) (hf) (f₂ : N ≃ O) (hf₂) :
    mapRange.equiv (ι := ι) (e.trans f₂) (by rw [Equiv.trans_apply, hf, hf₂]) =
      (mapRange.equiv e hf).trans (mapRange.equiv f₂ hf₂) := by ext; simp

@[simp, grind =]
/--
lemma `mapRange.equiv_symm` / 引理 `mapRange.equiv_symm`

English:
lemma mapRange.equiv_symm
  given: (e : M ≃ N) (hf)
  proof: rfl

中文:
引理 mapRange.equiv_symm
  条件: (e : M ≃ N) (hf)
  证明: rfl

Depends on / 依赖: e.symm, mapRange, mapRange.equiv
-/
lemma mapRange.equiv_symm (e : M ≃ N) (hf) :
    (mapRange.equiv (ι := ι) e hf).symm = mapRange.equiv e.symm (by simp [← hf]) := rfl

end Equiv

/-! ### Declarations about `embDomain` -/


section EmbDomain

variable [Zero M] [Zero N]

/--
Definition of `embDomain` / `embDomain` 的定义

English:
definition embDomain
  signature: (f : α ↪ β) (v : α ->₀ M)
  body: v.support.map f
  toFun b :=
    haveI := Classical.decEq β
    match v.support.1.find? (fun a => f a = b) (by intro x; grind) with
    | some a => v a
    | none => 0
  mem_support_toFun a₂ := by grind

@[simp]

中文:
定义 embDomain
  签名: (f : α ↪ β) (v : α ->₀ M)
  定义体: v.support.map f
  toFun b :=
    haveI := Classical.decEq β
    match v.support.1.find? (fun a => f a = b) (by intro x; grind) with
    | some a => v a
    | none => 0
  mem_support_toFun a₂ := by grind

@[simp]

Depends on / 依赖: support, v.support.map
-/
def embDomain (f : α ↪ β) (v : α ->₀ M) : β ->₀ M where
  support := v.support.map f
  toFun b :=
    haveI := Classical.decEq β
    match v.support.1.find? (fun a => f a = b) (by intro x; grind) with
    | some a => v a
    | none => 0
  mem_support_toFun a₂ := by grind

@[simp]
/--
theorem `support_embDomain` / 定理 `support_embDomain`

English:
theorem support_embDomain
  given: (f : α ↪ β) (v : α ->₀ M)
  statement: (embDomain f v).support = v.support.map f
  proof: rfl

@[simp]

中文:
定理 support_embDomain
  条件: (f : α ↪ β) (v : α ->₀ M)
  结论: (embDomain f v).support = v.support.map f
  证明: rfl

@[simp]
-/
theorem support_embDomain (f : α ↪ β) (v : α ->₀ M) : (embDomain f v).support = v.support.map f :=
  rfl

@[simp]
/--
theorem `embDomain_zero` / 定理 `embDomain_zero`

English:
theorem embDomain_zero
  given: (f : α ↪ β)
  statement: (embDomain f 0 : β ->₀ M) = 0
  proof: rfl

中文:
定理 embDomain_zero
  条件: (f : α ↪ β)
  结论: (embDomain f 0 : β ->₀ M) = 0
  证明: rfl
-/
theorem embDomain_zero (f : α ↪ β) : (embDomain f 0 : β ->₀ M) = 0 :=
  rfl

open scoped Classical in
@[grind =]
/--
theorem `embDomain_apply` / 定理 `embDomain_apply`

English:
theorem embDomain_apply
  given: (f : α ↪ β) (v : α ->₀ M) (b : β)
  proof: by
  simp only [embDomain, coe_mk]
  -- TODO: investigate why `grind` needs `split_ifs` first; this should never happen.
  split_ifs <;> grind

@[simp, grind =]

中文:
定理 embDomain_apply
  条件: (f : α ↪ β) (v : α ->₀ M) (b : β)
  证明: by
  simp only [embDomain, coe_mk]
  -- TODO: investigate why `grind` needs `split_ifs` first; this should never happen.
  split_ifs <;> grind

@[simp, grind =]

Depends on / 依赖: coe_mk, embDomain
-/
theorem embDomain_apply (f : α ↪ β) (v : α ->₀ M) (b : β) :
    embDomain f v b = if h : exists a, f a = b then v h.choose else 0 := by
  simp only [embDomain, coe_mk]
  -- TODO: investigate why `grind` needs `split_ifs` first; this should never happen.
  split_ifs <;> grind

@[simp, grind =]
/--
theorem `embDomain_apply_self` / 定理 `embDomain_apply_self`

English:
theorem embDomain_apply_self
  given: (f : α ↪ β) (v : α ->₀ M) (a : α)
  statement: embDomain f v (f a) = v a
  proof: by
  simp_rw [embDomain, coe_mk]
  grind

@[grind =>]

中文:
定理 embDomain_apply_self
  条件: (f : α ↪ β) (v : α ->₀ M) (a : α)
  结论: embDomain f v (f a) = v a
  证明: by
  simp_rw [embDomain, coe_mk]
  grind

@[grind =>]

Depends on / 依赖: coe_mk, embDomain, simp_rw
-/
theorem embDomain_apply_self (f : α ↪ β) (v : α ->₀ M) (a : α) : embDomain f v (f a) = v a := by
  simp_rw [embDomain, coe_mk]
  grind

@[grind =>]
/--
theorem `embDomain_of_notMem_range` / 定理 `embDomain_of_notMem_range`

English:
theorem embDomain_of_notMem_range
  given: (f : α ↪ β) (v : α ->₀ M) (a : β) (h : a ∉ Set.range f)
  proof: by grind [embDomain]

@[deprecated (since := "2026-07-15")] alias embDomain_notin_range := embDomain_of_notMem_range

中文:
定理 embDomain_of_notMem_range
  条件: (f : α ↪ β) (v : α ->₀ M) (a : β) (h : a ∉ Set.range f)
  证明: by grind [embDomain]

@[deprecated (since := "2026-07-15")] alias embDomain_notin_range := embDomain_of_notMem_range

Depends on / 依赖: embDomain
-/
theorem embDomain_of_notMem_range (f : α ↪ β) (v : α ->₀ M) (a : β) (h : a ∉ Set.range f) :
    embDomain f v a = 0 := by grind [embDomain]

@[deprecated (since := "2026-07-15")] alias embDomain_notin_range := embDomain_of_notMem_range

/--
theorem `embDomain_injective` / 定理 `embDomain_injective`

English:
theorem embDomain_injective
  given: (f : α ↪ β)
  statement: Function.Injective (embDomain f : (α ->₀ M) -> β ->₀ M)
  proof: fun l₁ l₂ h => ext fun a => by simpa only [embDomain_apply_self] using DFunLike.ext_iff.1 h (f a)

@[simp]

中文:
定理 embDomain_injective
  条件: (f : α ↪ β)
  结论: Function.Injective (embDomain f : (α ->₀ M) -> β ->₀ M)
  证明: fun l₁ l₂ h => ext fun a => by simpa only [embDomain_apply_self] using DFunLike.ext_iff.1 h (f a)

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, embDomain_apply_self, ext_iff
-/
theorem embDomain_injective (f : α ↪ β) : Function.Injective (embDomain f : (α ->₀ M) -> β ->₀ M) :=
  fun l₁ l₂ h => ext fun a => by simpa only [embDomain_apply_self] using DFunLike.ext_iff.1 h (f a)

@[simp]
/--
theorem `embDomain_inj` / 定理 `embDomain_inj`

English:
theorem embDomain_inj
  given: {f : α ↪ β} {l₁ l₂ : α ->₀ M}
  statement: embDomain f l₁ = embDomain f l₂ ↔ l₁ = l₂
  proof: (embDomain_injective f).eq_iff

@[simp]

中文:
定理 embDomain_inj
  条件: {f : α ↪ β} {l₁ l₂ : α ->₀ M}
  结论: embDomain f l₁ = embDomain f l₂ ↔ l₁ = l₂
  证明: (embDomain_injective f).eq_iff

@[simp]

Depends on / 依赖: embDomain_injective, eq_iff
-/
theorem embDomain_inj {f : α ↪ β} {l₁ l₂ : α ->₀ M} : embDomain f l₁ = embDomain f l₂ ↔ l₁ = l₂ :=
  (embDomain_injective f).eq_iff

@[simp]
/--
theorem `embDomain_eq_zero` / 定理 `embDomain_eq_zero`

English:
theorem embDomain_eq_zero
  given: {f : α ↪ β} {l : α ->₀ M}
  statement: embDomain f l = 0 ↔ l = 0
  proof: (embDomain_injective f).eq_iff' embDomain_zero f

中文:
定理 embDomain_eq_zero
  条件: {f : α ↪ β} {l : α ->₀ M}
  结论: embDomain f l = 0 ↔ l = 0
  证明: (embDomain_injective f).eq_iff' embDomain_zero f

Depends on / 依赖: embDomain_injective, embDomain_zero, eq_iff
-/
theorem embDomain_eq_zero {f : α ↪ β} {l : α ->₀ M} : embDomain f l = 0 ↔ l = 0 :=
(embDomain_injective f).eq_iff' embDomain_zero f

/--
theorem `embDomain_mapRange` / 定理 `embDomain_mapRange`

English:
theorem embDomain_mapRange
  given: (f : α ↪ β) (g : M -> N) (p : α ->₀ M) (hg : g 0 = 0)
  proof: by grind

@[simp]

中文:
定理 embDomain_mapRange
  条件: (f : α ↪ β) (g : M -> N) (p : α ->₀ M) (hg : g 0 = 0)
  证明: by grind

@[simp]
-/
theorem embDomain_mapRange (f : α ↪ β) (g : M -> N) (p : α ->₀ M) (hg : g 0 = 0) :
    embDomain f (mapRange g hg p) = mapRange g hg (embDomain f p) := by grind

@[simp]
/--
lemma `embDomain_refl` / 引理 `embDomain_refl`

English:
lemma embDomain_refl
  statement: embDomain (M := M) (Function.Embedding.refl α) = id
  proof: by
  ext; simp [embDomain_apply]

中文:
引理 embDomain_refl
  结论: embDomain (M := M) (Function.Embedding.refl α) = id
  证明: by
  ext; simp [embDomain_apply]

Depends on / 依赖: Embedding, Function, Function.Embedding.refl, embDomain_apply
-/
lemma embDomain_refl : embDomain (M := M) (Function.Embedding.refl α) = id := by
  ext; simp [embDomain_apply]

end EmbDomain

/-! ### Declarations about `zipWith` -/


section ZipWith

variable [Zero M] [Zero N] [Zero O]

/--
Definition of `zipWith` / `zipWith` 的定义

English:
definition zipWith
  signature: (f : M -> N -> O) (hf : f 0 0 = 0) (g₁ : α ->₀ M) (g₂ : α ->₀ N)
  body: onFinset
    (haveI := Classical.decEq α; g₁.support union g₂.support)
    (fun a => f (g₁ a) (g₂ a))
    fun a (H : f _ _ != 0) => by
      classical
      grind

@[simp, grind =]

中文:
定义 zipWith
  签名: (f : M -> N -> O) (hf : f 0 0 = 0) (g₁ : α ->₀ M) (g₂ : α ->₀ N)
  定义体: onFinset
    (haveI := Classical.decEq α; g₁.support union g₂.support)
    (fun a => f (g₁ a) (g₂ a))
    fun a (H : f _ _ != 0) => by
      classical
      grind

@[simp, grind =]

Depends on / 依赖: Classical, Classical.decEq, classical, onFinset, support
-/
def zipWith (f : M -> N -> O) (hf : f 0 0 = 0) (g₁ : α ->₀ M) (g₂ : α ->₀ N) : α ->₀ O :=
  onFinset
    (haveI := Classical.decEq α; g₁.support union g₂.support)
    (fun a => f (g₁ a) (g₂ a))
    fun a (H : f _ _ != 0) => by
      classical
      grind

@[simp, grind =]
/--
theorem `zipWith_apply` / 定理 `zipWith_apply`

English:
theorem zipWith_apply
  given: {f : M -> N -> O} {hf : f 0 0 = 0} {g₁ : α ->₀ M} {g₂ : α ->₀ N} {a : α}
  proof: rfl

中文:
定理 zipWith_apply
  条件: {f : M -> N -> O} {hf : f 0 0 = 0} {g₁ : α ->₀ M} {g₂ : α ->₀ N} {a : α}
  证明: rfl
-/
theorem zipWith_apply {f : M -> N -> O} {hf : f 0 0 = 0} {g₁ : α ->₀ M} {g₂ : α ->₀ N} {a : α} :
    zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a) :=
  rfl

/--
theorem `support_zipWith` / 定理 `support_zipWith`

English:
theorem support_zipWith
  statement: [D : DecidableEq α] {f : M -> N -> O} {hf : f 0 0 = 0} {g₁ : α ->₀ M}
  proof: by
  convert! support_onFinset_subset

中文:
定理 support_zipWith
  结论: [D : DecidableEq α] {f : M -> N -> O} {hf : f 0 0 = 0} {g₁ : α ->₀ M}
  证明: by
  convert! support_onFinset_subset

Depends on / 依赖: convert, support_onFinset_subset
-/
theorem support_zipWith [D : DecidableEq α] {f : M -> N -> O} {hf : f 0 0 = 0} {g₁ : α ->₀ M}
    {g₂ : α ->₀ N} : (zipWith f hf g₁ g₂).support subseteq g₁.support union g₂.support := by
  convert! support_onFinset_subset

end ZipWith

end Finsupp
