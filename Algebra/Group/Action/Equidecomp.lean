/-
Copyright (c) 2024 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Equidecompositions

This file develops the basic theory of equidecompositions.

## Main Definitions

Let `G` be a group acting on a space `X`, and `A B : Set X`.

An *equidecomposition* of `A` and `B` is typically defined as a finite partition of `A` together
with a finite list of elements of `G` of the same size such that applying each element to the
matching piece of the partition yields a partition of `B`.

This yields a bijection `f : A ≃ B` where, given `a : A`, `f a = γ • a` for `γ : G` the group
element for `a`'s piece of the partition. Reversing this is easy, and so we get an equivalent
(up to the choice of group elements) definition: an *Equidecomposition* of `A` and `B` is a
bijection `f : A ≃ B` such that for some `S : Finset G`, `f a ∈ S • a` for all `a`.

We take this as our definition as it is easier to work with. It is implemented as an element
`PartialEquiv X X` with source `A` and target `B`.

## Implementation Notes

* Equidecompositions are implemented as elements of `PartialEquiv X X` together with a
  `Finset` of elements of the acting group and a proof that every point in the source is moved
  by an element in the finset.

* The requirement that `G` be a group is relaxed where possible.

* We introduce a non-standard predicate, `IsDecompOn`, to state that a function satisfies the main
  combinatorial property of equidecompositions, even if it is not injective or surjective.

## TODO

* Prove that if two sets equidecompose into subsets of each other, they are equidecomposable
  (Schroeder-Bernstein type theorem)
* Define equidecomposability into subsets as a preorder on sets and
  prove that its induced equivalence relation is equidecomposability.
* Prove the definition of equidecomposition used here is equivalent to the more familiar one
  using partitions.

-/

@[expose] public section

variable {X G : Type*} {A B C : Set X}

open Function Set Pointwise PartialEquiv

namespace Equidecomp

section SMul

variable [SMul G X]

/--
Definition of `IsDecompOn` / `IsDecompOn` 的定义

English:
definition IsDecompOn
  signature: (f : X -> X) (A : Set X) (S : Finset G)
  body: forall a in A, exists g in S, f a = g • a

中文:
定义 IsDecompOn
  签名: (f : X -> X) (A : 集合 X) (S : 有限集 G)
  定义体: forall a in A, exists g in S, f a = g • a
-/
def IsDecompOn (f : X -> X) (A : Set X) (S : Finset G) : Prop := forall a in A, exists g in S, f a = g • a

variable (X G)

/--
Definition of `_root_.Equidecomp` / `_root_.Equidecomp` 的定义

English:
structure _root_.Equidecomp
  parameters: extends PartialEquiv X X
  extends: PartialEquiv X X
  axioms and operations (1):
    - isDecompOn' : exists S : Finset G, IsDecompOn toFun source S

中文:
结构 _root_.Equidecomp
  参数: extends 部分等价 X X
  继承: 部分等价 X X
  公理与运算 (1 个):
    - isDecompOn' : 存在 S : 有限集 G, IsDecompOn toFun source S
-/
structure _root_.Equidecomp extends PartialEquiv X X where
  isDecompOn' : exists S : Finset G, IsDecompOn toFun source S

variable {X G}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (Equidecomp X G) fun _ => X -> X
  body: ⟨fun f => f.toFun⟩

中文:
实例 :
  签名: CoeFun (Equidecomp X G) fun _ => X -> X
  定义体: ⟨fun f => f.toFun⟩

Depends on / 依赖: f.toFun
-/
instance : CoeFun (Equidecomp X G) fun _ => X -> X := ⟨fun f => f.toFun⟩

/-- A finite set of group elements witnessing that `f` is an equidecomposition. -/
noncomputable
/--
Definition of `witness` / `witness` 的定义

English:
definition witness
  signature: (f : Equidecomp X G)
  body: f.isDecompOn'.choose

中文:
定义 witness
  签名: (f : Equidecomp X G)
  定义体: f.isDecompOn'.choose

Depends on / 依赖: f.isDecompOn, isDecompOn
-/
def witness (f : Equidecomp X G) : Finset G := f.isDecompOn'.choose

/--
theorem `isDecompOn` / 定理 `isDecompOn`

English:
theorem isDecompOn
  given: (f : Equidecomp X G)
  statement: IsDecompOn f f.source f.witness
  proof: f.isDecompOn'.choose_spec

中文:
定理 isDecompOn
  条件: (f : Equidecomp X G)
  结论: IsDecompOn f f.source f.witness
  证明: f.isDecompOn'.choose_spec

Depends on / 依赖: choose_spec, f.isDecompOn, isDecompOn
-/
theorem isDecompOn (f : Equidecomp X G) : IsDecompOn f f.source f.witness :=
  f.isDecompOn'.choose_spec

/--
theorem `apply_mem_target` / 定理 `apply_mem_target`

English:
theorem apply_mem_target
  given: {f : Equidecomp X G} {x : X} (h : x in f.source)
  proof: by simp [h]

中文:
定理 apply_mem_target
  条件: {f : Equidecomp X G} {x : X} (h : x in f.source)
  证明: by simp [h]
-/
theorem apply_mem_target {f : Equidecomp X G} {x : X} (h : x in f.source) :
    f x in f.target := by simp [h]

/--
theorem `toPartialEquiv_injective` / 定理 `toPartialEquiv_injective`

English:
theorem toPartialEquiv_injective
  statement: Injective toPartialEquiv (X := X) (G := G)
  proof: by
  intro ⟨_, _, _⟩ _ _
  congr

中文:
定理 toPartialEquiv_injective
  结论: 单射 toPartialEquiv (X := X) (G := G)
  证明: by
  intro ⟨_, _, _⟩ _ _
  congr
-/
theorem toPartialEquiv_injective : Injective toPartialEquiv (X := X) (G := G) := by
  intro ⟨_, _, _⟩ _ _
  congr

/--
theorem `IsDecompOn.mono` / 定理 `IsDecompOn.mono`

English:
theorem IsDecompOn.mono
  statement: {f f' : X -> X} {A A' : Set X} {S : Finset G} (h : IsDecompOn f A S)
  proof: by
  intro a ha
  rw [← hf' ha]
  exact h a (hA' ha)

中文:
定理 IsDecompOn.mono
  结论: {f f' : X -> X} {A A' : 集合 X} {S : 有限集 G} (h : IsDecompOn f A S)
  证明: by
  intro a ha
  rw [← hf' ha]
  exact h a (hA' ha)
-/
theorem IsDecompOn.mono {f f' : X -> X} {A A' : Set X} {S : Finset G} (h : IsDecompOn f A S)
    (hA' : A' subseteq A) (hf' : EqOn f f' A') : IsDecompOn f' A' S := by
  intro a ha
  rw [← hf' ha]
  exact h a (hA' ha)

/-- The restriction of an equidecomposition as an equidecomposition. -/
@[simps!]
/--
Definition of `restr` / `restr` 的定义

English:
definition restr
  signature: (f : Equidecomp X G) (A : Set X)
  body: f.toPartialEquiv.restr A
  isDecompOn' := ⟨f.witness,
    f.isDecompOn.mono (source_restr_subset_source _ _) fun _ => congrFun rfl⟩

@[simp]

中文:
定义 restr
  签名: (f : Equidecomp X G) (A : 集合 X)
  定义体: f.toPartialEquiv.restr A
  isDecompOn' := ⟨f.witness,
    f.isDecompOn.mono (source_restr_subset_source _ _) fun _ => congrFun rfl⟩

@[simp]

Depends on / 依赖: f.toPartialEquiv.restr, toPartialEquiv
-/
def restr (f : Equidecomp X G) (A : Set X) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.restr A
  isDecompOn' := ⟨f.witness,
    f.isDecompOn.mono (source_restr_subset_source _ _) fun _ => congrFun rfl⟩

@[simp]
/--
theorem `toPartialEquiv_restr` / 定理 `toPartialEquiv_restr`

English:
theorem toPartialEquiv_restr
  given: (f : Equidecomp X G) (A : Set X)
  proof: rfl

中文:
定理 toPartialEquiv_restr
  条件: (f : Equidecomp X G) (A : 集合 X)
  证明: rfl
-/
theorem toPartialEquiv_restr (f : Equidecomp X G) (A : Set X) :
    (f.restr A).toPartialEquiv = f.toPartialEquiv.restr A := rfl

/--
theorem `source_restr` / 定理 `source_restr`

English:
theorem source_restr
  given: (f : Equidecomp X G) {A : Set X} (hA : A subseteq f.source)
  proof: by rw [restr_source, inter_eq_self_of_subset_right hA]

中文:
定理 source_restr
  条件: (f : Equidecomp X G) {A : 集合 X} (hA : A subseteq f.source)
  证明: by rw [restr_source, inter_eq_self_of_subset_right hA]

Depends on / 依赖: inter_eq_self_of_subset_right, restr_source
-/
theorem source_restr (f : Equidecomp X G) {A : Set X} (hA : A subseteq f.source) :
    (f.restr A).source = A := by rw [restr_source, inter_eq_self_of_subset_right hA]

/--
theorem `restr_of_source_subset` / 定理 `restr_of_source_subset`

English:
theorem restr_of_source_subset
  given: {f : Equidecomp X G} {A : Set X} (hA : f.source subseteq A)
  proof: by
  apply toPartialEquiv_injective
  rw [toPartialEquiv_restr]; rw [PartialEquiv.restr_eq_of_source_subset hA]

@[simp]

中文:
定理 restr_of_source_subset
  条件: {f : Equidecomp X G} {A : 集合 X} (hA : f.source subseteq A)
  证明: by
  apply toPartialEquiv_injective
  rw [toPartialEquiv_restr]; rw [PartialEquiv.restr_eq_of_source_subset hA]

@[simp]

Depends on / 依赖: PartialEquiv, PartialEquiv.restr_eq_of_source_subset, restr_eq_of_source_subset, toPartialEquiv_injective, toPartialEquiv_restr
-/
theorem restr_of_source_subset {f : Equidecomp X G} {A : Set X} (hA : f.source subseteq A) :
    f.restr A = f := by
  apply toPartialEquiv_injective
  rw [toPartialEquiv_restr]; rw [PartialEquiv.restr_eq_of_source_subset hA]

@[simp]
/--
theorem `restr_univ` / 定理 `restr_univ`

English:
theorem restr_univ
  given: (f : Equidecomp X G)
  statement: f.restr univ = f
  proof: restr_of_source_subset subset_univ _

中文:
定理 restr_univ
  条件: (f : Equidecomp X G)
  结论: f.restr univ = f
  证明: restr_of_source_subset subset_univ _

Depends on / 依赖: restr_of_source_subset, subset_univ
-/
theorem restr_univ (f : Equidecomp X G) : f.restr univ = f :=
restr_of_source_subset subset_univ _

end SMul

section Monoid

variable [Monoid G] [MulAction G X]

variable (X G)

/-- The identity function is an equidecomposition of the space with itself. -/
@[simps toPartialEquiv]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : Equidecomp X G where
  body: .refl _
  isDecompOn' := ⟨{1}, by simp [IsDecompOn]⟩

中文:
定义 refl
  签名: : Equidecomp X G where
  定义体: .refl _
  isDecompOn' := ⟨{1}, by simp [IsDecompOn]⟩
-/
def refl : Equidecomp X G where
  toPartialEquiv := .refl _
  isDecompOn' := ⟨{1}, by simp [IsDecompOn]⟩

variable {X} {G}

open scoped Classical in
/--
theorem `IsDecompOn.comp'` / 定理 `IsDecompOn.comp'`

English:
theorem IsDecompOn.comp'
  statement: {g f : X -> X} {B A : Set X} {T S : Finset G}
  proof: by
  intro _ ⟨aA, aB⟩
  rcases hf _ aA with ⟨γ, γ_mem, hγ⟩
  rcases hg _ aB with ⟨δ, δ_mem, hδ⟩
  use δ * γ, Finset.mul_mem_mul δ_mem γ_mem
  rwa [mul_smul, ← hγ]

中文:
定理 IsDecompOn.comp'
  结论: {g f : X -> X} {B A : 集合 X} {T S : 有限集 G}
  证明: by
  intro _ ⟨aA, aB⟩
  rcases hf _ aA with ⟨γ, γ_mem, hγ⟩
  rcases hg _ aB with ⟨δ, δ_mem, hδ⟩
  use δ * γ, Finset.mul_mem_mul δ_mem γ_mem
  rwa [mul_smul, ← hγ]

Depends on / 依赖: Finset, Finset.mul_mem_mul, mul_mem_mul, mul_smul
-/
theorem IsDecompOn.comp' {g f : X -> X} {B A : Set X} {T S : Finset G}
    (hg : IsDecompOn g B T) (hf : IsDecompOn f A S) :
    IsDecompOn (g ∘ f) (A inter f ⁻¹' B) (T * S) := by
  intro _ ⟨aA, aB⟩
  rcases hf _ aA with ⟨γ, γ_mem, hγ⟩
  rcases hg _ aB with ⟨δ, δ_mem, hδ⟩
  use δ * γ, Finset.mul_mem_mul δ_mem γ_mem
  rwa [mul_smul, ← hγ]

open scoped Classical in
/--
theorem `IsDecompOn.comp` / 定理 `IsDecompOn.comp`

English:
theorem IsDecompOn.comp
  statement: {g f : X -> X} {B A : Set X} {T S : Finset G}
  proof: by
  rw [left_eq_inter.mpr h]
  exact hg.comp' hf

中文:
定理 IsDecompOn.comp
  结论: {g f : X -> X} {B A : 集合 X} {T S : 有限集 G}
  证明: by
  rw [left_eq_inter.mpr h]
  exact hg.comp' hf

Depends on / 依赖: hg.comp, left_eq_inter, left_eq_inter.mpr
-/
theorem IsDecompOn.comp {g f : X -> X} {B A : Set X} {T S : Finset G}
    (hg : IsDecompOn g B T) (hf : IsDecompOn f A S) (h : MapsTo f A B) :
    IsDecompOn (g ∘ f) A (T * S) := by
  rw [left_eq_inter.mpr h]
  exact hg.comp' hf

/-- The composition of two equidecompositions as an equidecomposition. -/
@[simps toPartialEquiv, trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (f g : Equidecomp X G)
  body: f.toPartialEquiv.trans g.toPartialEquiv
  isDecompOn' := by classical exact ⟨g.witness * f.witness, g.isDecompOn.comp' f.isDecompOn⟩

中文:
定义 trans
  签名: (f g : Equidecomp X G)
  定义体: f.toPartialEquiv.trans g.toPartialEquiv
  isDecompOn' := by classical exact ⟨g.witness * f.witness, g.isDecompOn.comp' f.isDecompOn⟩

Depends on / 依赖: f.toPartialEquiv.trans, g.toPartialEquiv, toPartialEquiv
-/
noncomputable def trans (f g : Equidecomp X G) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.trans g.toPartialEquiv
  isDecompOn' := by classical exact ⟨g.witness * f.witness, g.isDecompOn.comp' f.isDecompOn⟩

end Monoid

section Group

variable [Group G] [MulAction G X]

open scoped Classical in
/--
theorem `IsDecompOn.of_leftInvOn` / 定理 `IsDecompOn.of_leftInvOn`

English:
theorem IsDecompOn.of_leftInvOn
  statement: {f g : X -> X} {A : Set X} {S : Finset G}
  proof: by
  rintro _ ⟨a, ha, rfl⟩
  rcases hf a ha with ⟨γ, γ_mem, hγ⟩
  use γ⁻¹, Finset.inv_mem_inv γ_mem
  rw [hγ]; rw [inv_smul_smul]; rw [← hγ]; rw [h ha]

中文:
定理 IsDecompOn.of_leftInvOn
  结论: {f g : X -> X} {A : 集合 X} {S : 有限集 G}
  证明: by
  rintro _ ⟨a, ha, rfl⟩
  rcases hf a ha with ⟨γ, γ_mem, hγ⟩
  use γ⁻¹, Finset.inv_mem_inv γ_mem
  rw [hγ]; rw [inv_smul_smul]; rw [← hγ]; rw [h ha]

Depends on / 依赖: Finset, Finset.inv_mem_inv, inv_mem_inv, inv_smul_smul
-/
theorem IsDecompOn.of_leftInvOn {f g : X -> X} {A : Set X} {S : Finset G}
    (hf : IsDecompOn f A S) (h : LeftInvOn g f A) : IsDecompOn g (f '' A) S⁻¹ := by
  rintro _ ⟨a, ha, rfl⟩
  rcases hf a ha with ⟨γ, γ_mem, hγ⟩
  use γ⁻¹, Finset.inv_mem_inv γ_mem
  rw [hγ]; rw [inv_smul_smul]; rw [← hγ]; rw [h ha]

/-- The inverse function of an equidecomposition as an equidecomposition. -/
@[symm, simps toPartialEquiv]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (f : Equidecomp X G)
  body: f.toPartialEquiv.symm
  isDecompOn' := by classical exact ⟨f.witness⁻¹, by
    convert! f.isDecompOn.of_leftInvOn f.leftInvOn
    rw [image_source_eq_target]; rw [symm_source]⟩

中文:
定义 symm
  签名: (f : Equidecomp X G)
  定义体: f.toPartialEquiv.symm
  isDecompOn' := by classical exact ⟨f.witness⁻¹, by
    convert! f.isDecompOn.of_leftInvOn f.leftInvOn
    rw [image_source_eq_target]; rw [symm_source]⟩

Depends on / 依赖: f.toPartialEquiv.symm, toPartialEquiv
-/
noncomputable def symm (f : Equidecomp X G) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.symm
  isDecompOn' := by classical exact ⟨f.witness⁻¹, by
    convert! f.isDecompOn.of_leftInvOn f.leftInvOn
    rw [image_source_eq_target]; rw [symm_source]⟩

/--
theorem `map_target` / 定理 `map_target`

English:
theorem map_target
  given: {f : Equidecomp X G} {x : X} (h : x in f.target)
  proof: f.toPartialEquiv.map_target h

中文:
定理 map_target
  条件: {f : Equidecomp X G} {x : X} (h : x in f.target)
  证明: f.toPartialEquiv.map_target h

Depends on / 依赖: f.toPartialEquiv.map_target, map_target, toPartialEquiv
-/
theorem map_target {f : Equidecomp X G} {x : X} (h : x in f.target) :
    f.symm x in f.source := f.toPartialEquiv.map_target h

/--
theorem `left_inv` / 定理 `left_inv`

English:
theorem left_inv
  given: {f : Equidecomp X G} {x : X} (h : x in f.source)
  proof: by simp [h]

中文:
定理 left_inv
  条件: {f : Equidecomp X G} {x : X} (h : x in f.source)
  证明: by simp [h]
-/
theorem left_inv {f : Equidecomp X G} {x : X} (h : x in f.source) :
    f.toPartialEquiv.symm (f x) = x := by simp [h]

/--
theorem `right_inv` / 定理 `right_inv`

English:
theorem right_inv
  given: {f : Equidecomp X G} {x : X} (h : x in f.target)
  proof: by simp [h]

@[simp]

中文:
定理 right_inv
  条件: {f : Equidecomp X G} {x : X} (h : x in f.target)
  证明: by simp [h]

@[simp]
-/
theorem right_inv {f : Equidecomp X G} {x : X} (h : x in f.target) :
    f (f.toPartialEquiv.symm x) = x := by simp [h]

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (f : Equidecomp X G)
  statement: f.symm.symm = f
  proof: rfl

中文:
定理 symm_symm
  条件: (f : Equidecomp X G)
  结论: f.symm.symm = f
  证明: rfl
-/
theorem symm_symm (f : Equidecomp X G) : f.symm.symm = f := rfl

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  statement: (f : Equidecomp X G) {x y} (hx : x in f.toPartialEquiv.target)
  proof: f.toPartialEquiv.symm_apply_eq hy hx

中文:
定理 symm_apply_eq
  结论: (f : Equidecomp X G) {x y} (hx : x in f.toPartialEquiv.target)
  证明: f.toPartialEquiv.symm_apply_eq hy hx

Depends on / 依赖: f.toPartialEquiv.symm_apply_eq, symm_apply_eq, toPartialEquiv
-/
theorem symm_apply_eq (f : Equidecomp X G) {x y} (hx : x in f.toPartialEquiv.target)
    (hy : y in f.toPartialEquiv.source) : f.symm x = y ↔ x = f y :=
  f.toPartialEquiv.symm_apply_eq hy hx

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  statement: (f : Equidecomp X G) {x y} (hx : x in f.toPartialEquiv.target)
  proof: f.toPartialEquiv.eq_symm_apply hy hx

中文:
定理 eq_symm_apply
  结论: (f : Equidecomp X G) {x y} (hx : x in f.toPartialEquiv.target)
  证明: f.toPartialEquiv.eq_symm_apply hy hx

Depends on / 依赖: eq_symm_apply, f.toPartialEquiv.eq_symm_apply, toPartialEquiv
-/
theorem eq_symm_apply (f : Equidecomp X G) {x y} (hx : x in f.toPartialEquiv.target)
    (hy : y in f.toPartialEquiv.source) : y = f.symm x ↔ f y = x :=
  f.toPartialEquiv.eq_symm_apply hy hx

/--
theorem `symm_involutive` / 定理 `symm_involutive`

English:
theorem symm_involutive
  statement: Function.Involutive (symm : Equidecomp X G -> _)
  proof: symm_symm

中文:
定理 symm_involutive
  结论: 函数.对合 (symm : Equidecomp X G -> _)
  证明: symm_symm

Depends on / 依赖: symm_symm
-/
theorem symm_involutive : Function.Involutive (symm : Equidecomp X G -> _) := symm_symm

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (symm : Equidecomp X G -> _)
  proof: symm_involutive.bijective

@[simp]

中文:
定理 symm_bijective
  结论: 函数.双射 (symm : Equidecomp X G -> _)
  证明: symm_involutive.bijective

@[simp]

Depends on / 依赖: Quotient, Quotient.recOnSubsingleton, bijective, conjugatesOf, conjugatesOf.fintype, fintype, recOnSubsingleton, symm_involutive, symm_involutive.bijective
-/
theorem symm_bijective : Function.Bijective (symm : Equidecomp X G -> _) := symm_involutive.bijective

@[simp]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (refl X G).symm = refl X G
  proof: rfl

@[simp]

中文:
定理 refl_symm
  结论: (refl X G).symm = refl X G
  证明: rfl

@[simp]
-/
theorem refl_symm : (refl X G).symm = refl X G := rfl

@[simp]
/--
theorem `restr_refl_symm` / 定理 `restr_refl_symm`

English:
theorem restr_refl_symm
  given: (A : Set X)
  proof: rfl

中文:
定理 restr_refl_symm
  条件: (A : 集合 X)
  证明: rfl
-/
theorem restr_refl_symm (A : Set X) :
    ((Equidecomp.refl X G).restr A).symm = (Equidecomp.refl X G).restr A := rfl

end Group

end Equidecomp
