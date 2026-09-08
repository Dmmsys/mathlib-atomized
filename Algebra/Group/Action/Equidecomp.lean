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

/-- Let `G` act on a space `X` and `A : Set X`. We say `f : X → X` is a decomposition on `A`
as witnessed by some `S : Finset G` if for all `a ∈ A`, the value `f a` can be obtained
by applying some element of `S` to `a` instead.

More familiarly, the restriction of `f` to `A` is the result of partitioning `A` into finitely many
pieces, then applying a single element of `G` to each piece. -/
/-
**Equidecomp.IsDecompOn** 是 Mathlib 中的一个定义，位于命名空间 `Equidecomp`。
形式化陈述：IsDecompOn (f : X -> X) (A : Set X) (S : Finset G) : Prop
参数：f : X -> X；A : Set X；S : Finset G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `G` act on a space `X` and `A : Set X`. We say `f : X → X` is a decompositio
n on `A`
as witnessed by some `S : Finset G` if for all `a ∈ A`, the value `f a` can be o
btained
by applying some element of `S` to `a` instead.

More familiarly, the restriction of `f` to `A` is the result of partitioning `A`
 into finitely many
pieces, then applying a single element of `G` to each piece.
-/
def IsDecompOn (f : X → X) (A : Set X) (S : Finset G) : Prop := ∀ a ∈ A, ∃ g ∈ S, f a = g • a

variable (X G)

/-- Let `G` act on a space `X`. An `Equidecomposition` with respect to `X` and `G` is a partial
bijection `f : PartialEquiv X X` with the property that for some set `elements : Finset G`,
(which we record), for each `a ∈ f.source`, `f a` can be obtained by applying some `g ∈ elements`
instead. We call `f` an equidecomposition of `f.source` with `f.target`.

More familiarly, `f` is the result of partitioning `f.source` into finitely many pieces,
then applying a single element of `G` to each to get a partition of `f.target`.
-/
/-
**Equidecomp._root_.Equidecomp** 是 Mathlib 中的一个结构，位于命名空间 `Equidecomp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `G` act on a space `X`. An `Equidecomposition` with respect to `X` and `G` i
s a partial
bijection `f : PartialEquiv X X` with the property that for some set `elements :
 Finset G`,
(which we record), for each `a ∈ f.source`, `f a` can be obtained by applying so
me `g ∈ elements`
instead. We call `f` an equidecomposition of `f.source` with `f.target`.

More familiarly, `f` is the result of partitioning `f.source` into finitely many
 pieces,
then applying a single element of `G` to each to get a partition of `f.target`.
-/
structure _root_.Equidecomp extends PartialEquiv X X where
  isDecompOn' : ∃ S : Finset G, IsDecompOn toFun source S

variable {X G}

/-- Note that `Equidecomp X G` is not `FunLike`. -/
/-
**Equidecomp.** 是 Mathlib 中的一个实例，位于命名空间 `Equidecomp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that `Equidecomp X G` is not `FunLike`.
-/
instance : CoeFun (Equidecomp X G) fun _ => X → X := ⟨fun f => f.toFun⟩

/-- A finite set of group elements witnessing that `f` is an equidecomposition. -/
noncomputable
/-
**Equidecomp.witness** 是 Mathlib 中的一个定义，位于命名空间 `Equidecomp`。
形式化陈述：witness (f : Equidecomp X G) : Finset G
参数：f : Equidecomp X G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equidecomp.isDecompOn'`：∀ {X : Type u_1} {G : Type u_2} [inst : SMul G X
] (self : Equidecomp X G),   ∃ S, Equidecomp.IsDecompOn (↑self.toPartialEquiv) s
elf.source S
-/
def witness (f : Equidecomp X G) : Finset G := f.isDecompOn'.choose
/-
**Equidecomp.isDecompOn** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp`。
形式化陈述：isDecompOn (f : Equidecomp X G) : IsDecompOn f f.source f.witness
参数：f : Equidecomp X G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Equidecomp.isDecompOn'`：∀ {X : Type u_1} {G : Type u_2} [inst : SMul G X
] (self : Equidecomp X G),   ∃ S, Equidecomp.IsDecompOn (↑self.toPartialEquiv) s
elf.source S
-/
theorem isDecompOn (f : Equidecomp X G) : IsDecompOn f f.source f.witness :=
  f.isDecompOn'.choose_spec
/-
**Equidecomp.apply_mem_target** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp`。
形式化陈述：apply_mem_target {f : Equidecomp X G} {x : X} (h : x in f.source) : f x in
 f.target
参数：h : x in f.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem apply_mem_target {f : Equidecomp X G} {x : X} (h : x ∈ f.source) :
    f x ∈ f.target := by simp [h]
/-
**Equidecomp.toPartialEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp`。
形式化陈述：toPartialEquiv_injective : Injective toPartialEquiv (X
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPartialEquiv_injective : Injective <| toPartialEquiv (X := X) (G := G) := by
  intro ⟨_, _, _⟩ _ _
  congr
/-
**Equidecomp.IsDecompOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp.IsDecompOn`。
形式化陈述：∀ {X : Type u_1} {G : Type u_2} [inst : SMul G X] {f f' : X → X} {A A' : S
et X} {S : Finset G},   Equidecomp.IsDecompOn f A S → A' ⊆ A → Set.EqOn f f' A' 
→ Equidecomp.IsDecompOn f' A' S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsDecompOn.mono {f f' : X → X} {A A' : Set X} {S : Finset G} (h : IsDecompOn f A S)
    (hA' : A' ⊆ A) (hf' : EqOn f f' A') : IsDecompOn f' A' S := by
  intro a ha
  rw [← hf' ha]
  exact h a (hA' ha)

/-- The restriction of an equidecomposition as an equidecomposition. -/
@[simps!]
/-
**Equidecomp.restr** 是 Mathlib 中的一个定义，位于命名空间 `Equidecomp`。
形式化陈述：restr (f : Equidecomp X G) (A : Set X) : Equidecomp X G where toPartialEqu
iv
参数：f : Equidecomp X G；A : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of an equidecomposition as an equidecomposition.
-/
def restr (f : Equidecomp X G) (A : Set X) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.restr A
  isDecompOn' := ⟨f.witness,
    f.isDecompOn.mono (source_restr_subset_source _ _) fun _ ↦ congrFun rfl⟩

@[simp]
/-
**Equidecomp.toPartialEquiv_restr** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp`。
形式化陈述：toPartialEquiv_restr (f : Equidecomp X G) (A : Set X) : (f.restr A).toPart
ialEquiv = f.toPartialEquiv.restr A
参数：f : Equidecomp X G；A : Set X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPartialEquiv_restr (f : Equidecomp X G) (A : Set X) :
    (f.restr A).toPartialEquiv = f.toPartialEquiv.restr A := rfl
/-
**Equidecomp.source_restr** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp`。
形式化陈述：source_restr (f : Equidecomp X G) {A : Set X} (hA : A subseteq f.source) :
 (f.restr A).source = A
参数：f : Equidecomp X G；hA : A subseteq f.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equidecomp.restr_source`：∀ {X : Type u_1} {G : Type u_2} [inst : SMul G 
X] (f : Equidecomp X G) (A : Set X), (f.restr A).source = f.source ∩ A
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
-/
theorem source_restr (f : Equidecomp X G) {A : Set X} (hA : A ⊆ f.source) :
    (f.restr A).source = A := by rw [restr_source, inter_eq_self_of_subset_right hA]
/-
**Equidecomp.restr_of_source_subset** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp`。
形式化陈述：restr_of_source_subset {f : Equidecomp X G} {A : Set X} (hA : f.source sub
seteq A) : f.restr A = f
参数：hA : f.source subseteq A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equidecomp.toPartialEquiv_injective`：toPartialEquiv_injective : Injectiv
e toPartialEquiv (X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equidecomp.toPartialEquiv_restr`：toPartialEquiv_restr (f : Equidecomp X 
G) (A : Set X) : (f.restr A).toPartialEquiv = f.toPartialEquiv.restr A
· 使用定理 `PartialEquiv.restr_eq_of_source_subset`：restr_eq_of_source_subset {e : P
artialEquiv α β} {s : Set α} (h : e.source subseteq s) : e.restr s = e
-/
theorem restr_of_source_subset {f : Equidecomp X G} {A : Set X} (hA : f.source ⊆ A) :
    f.restr A = f := by
  apply toPartialEquiv_injective
  rw [toPartialEquiv_restr, PartialEquiv.restr_eq_of_source_subset hA]

@[simp]
/-
**Equidecomp.restr_univ** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp`。
形式化陈述：restr_univ (f : Equidecomp X G) : f.restr univ = f
参数：f : Equidecomp X G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equidecomp.restr_of_source_subset`：restr_of_source_subset {f : Equidecom
p X G} {A : Set X} (hA : f.source subseteq A) : f.restr A = f
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem restr_univ (f : Equidecomp X G) : f.restr univ = f :=
  restr_of_source_subset <| subset_univ _

end SMul

section Monoid

variable [Monoid G] [MulAction G X]

variable (X G)

/-- The identity function is an equidecomposition of the space with itself. -/
@[simps toPartialEquiv]
/-
**Equidecomp.refl** 是 Mathlib 中的一个定义，位于命名空间 `Equidecomp`。
形式化陈述：refl : Equidecomp X G where toPartialEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity function is an equidecomposition of the space with itself.
-/
def refl : Equidecomp X G where
  toPartialEquiv := .refl _
  isDecompOn' := ⟨{1}, by simp [IsDecompOn]⟩

variable {X} {G}

open scoped Classical in
/-
**Equidecomp.IsDecompOn.comp'** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp.IsDecompOn`。
形式化陈述：∀ {X : Type u_1} {G : Type u_2} [inst : Monoid G] [inst_1 : MulAction G X]
 {g f : X → X} {B A : Set X} {T S : Finset G},   Equidecomp.IsDecompOn g B T → E
quidecomp.IsDecompOn f A S → Equidecomp.IsDecompOn (g ∘ f) (A ∩ f ⁻¹' B) (T * S)
参数：g ∘ f；A ∩ f ⁻¹' B；T * S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsDecompOn.comp' {g f : X → X} {B A : Set X} {T S : Finset G}
    (hg : IsDecompOn g B T) (hf : IsDecompOn f A S) :
    IsDecompOn (g ∘ f) (A ∩ f ⁻¹' B) (T * S) := by
  intro _ ⟨aA, aB⟩
  rcases hf _ aA with ⟨γ, γ_mem, hγ⟩
  rcases hg _ aB with ⟨δ, δ_mem, hδ⟩
  use δ * γ, Finset.mul_mem_mul δ_mem γ_mem
  rwa [mul_smul, ← hγ]

open scoped Classical in
/-
**Equidecomp.IsDecompOn.comp** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp.IsDecompOn`。
形式化陈述：∀ {X : Type u_1} {G : Type u_2} [inst : Monoid G] [inst_1 : MulAction G X]
 {g f : X → X} {B A : Set X} {T S : Finset G},   Equidecomp.IsDecompOn g B T → E
quidecomp.IsDecompOn f A S → Set.MapsTo f A B → Equidecomp.IsDecompOn (g ∘ f) A 
(T * S)
参数：g ∘ f；T * S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_eq_inter`：∀ {α : Type u} {s t : Set α}, s = s ∩ t ↔ s ⊆ t
· 使用定理 `Equidecomp.IsDecompOn.comp'`：∀ {X : Type u_1} {G : Type u_2} [inst : Mon
oid G] [inst_1 : MulAction G X] {g f : X → X} {B A : Set X} {T S : Finset G},   
Equidecomp.IsDeco…
-/
theorem IsDecompOn.comp {g f : X → X} {B A : Set X} {T S : Finset G}
    (hg : IsDecompOn g B T) (hf : IsDecompOn f A S) (h : MapsTo f A B) :
    IsDecompOn (g ∘ f) A (T * S) := by
  rw [left_eq_inter.mpr h]
  exact hg.comp' hf

/-- The composition of two equidecompositions as an equidecomposition. -/
@[simps toPartialEquiv, trans]
/-
**Equidecomp.trans** 是 Mathlib 中的一个定义，位于命名空间 `Equidecomp`。
形式化陈述：trans (f g : Equidecomp X G) : Equidecomp X G where toPartialEquiv
参数：f g : Equidecomp X G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two equidecompositions as an equidecomposition.
-/
noncomputable def trans (f g : Equidecomp X G) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.trans g.toPartialEquiv
  isDecompOn' := by classical exact ⟨g.witness * f.witness, g.isDecompOn.comp' f.isDecompOn⟩

end Monoid

section Group

variable [Group G] [MulAction G X]

open scoped Classical in
/-
**Equidecomp.IsDecompOn.of_leftInvOn** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp.IsDec
ompOn`。
形式化陈述：∀ {X : Type u_1} {G : Type u_2} [inst : Group G] [inst_1 : MulAction G X] 
{f g : X → X} {A : Set X} {S : Finset G},   Equidecomp.IsDecompOn f A S → Set.Le
ftInvOn g f A → Equidecomp.IsDecompOn g (f '' A) S⁻¹
参数：f '' A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inv_mem_inv`：inv_mem_inv (ha : a in s) : a⁻¹ in s⁻¹
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsDecompOn.of_leftInvOn {f g : X → X} {A : Set X} {S : Finset G}
    (hf : IsDecompOn f A S) (h : LeftInvOn g f A) : IsDecompOn g (f '' A) S⁻¹ := by
  rintro _ ⟨a, ha, rfl⟩
  rcases hf a ha with ⟨γ, γ_mem, hγ⟩
  use γ⁻¹, Finset.inv_mem_inv γ_mem
  rw [hγ, inv_smul_smul, ← hγ, h ha]

/-- The inverse function of an equidecomposition as an equidecomposition. -/
@[symm, simps toPartialEquiv]
/-
**Equidecomp.symm** 是 Mathlib 中的一个定义，位于命名空间 `Equidecomp`。
形式化陈述：symm (f : Equidecomp X G) : Equidecomp X G where toPartialEquiv
参数：f : Equidecomp X G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse function of an equidecomposition as an equidecomposition.
-/
noncomputable def symm (f : Equidecomp X G) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.symm
  isDecompOn' := by classical exact ⟨f.witness⁻¹, by
    convert! f.isDecompOn.of_leftInvOn f.leftInvOn
    rw [image_source_eq_target, symm_source]⟩
/-
**Equidecomp.map_target** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp`。
形式化陈述：map_target {f : Equidecomp X G} {x : X} (h : x in f.target) : f.symm x in 
f.source
参数：h : x in f.target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.map_target`：map_target {x : β} (h : x in e.target) : e.symm
 x in e.source
-/
theorem map_target {f : Equidecomp X G} {x : X} (h : x ∈ f.target) :
    f.symm x ∈ f.source := f.toPartialEquiv.map_target h
/-
**Equidecomp.left_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp`。
形式化陈述：left_inv {f : Equidecomp X G} {x : X} (h : x in f.source) : f.toPartialEqu
iv.symm (f x) = x
参数：h : x in f.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem left_inv {f : Equidecomp X G} {x : X} (h : x ∈ f.source) :
    f.toPartialEquiv.symm (f x) = x := by simp [h]
/-
**Equidecomp.right_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp`。
形式化陈述：right_inv {f : Equidecomp X G} {x : X} (h : x in f.target) : f (f.toPartia
lEquiv.symm x) = x
参数：h : x in f.target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem right_inv {f : Equidecomp X G} {x : X} (h : x ∈ f.target) :
    f (f.toPartialEquiv.symm x) = x := by simp [h]

@[simp]
/-
**Equidecomp.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp`。
形式化陈述：symm_symm (f : Equidecomp X G) : f.symm.symm = f
参数：f : Equidecomp X G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (f : Equidecomp X G) : f.symm.symm = f := rfl
/-
**Equidecomp.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp`。
形式化陈述：symm_apply_eq (f : Equidecomp X G) {x y} (hx : x in f.toPartialEquiv.targe
t) (hy : y in f.toPartialEquiv.source) : f.symm x = y ↔ x = f y
参数：f : Equidecomp X G；hx : x in f.toPartialEquiv.target；hy : y in f.toPartialEqu
iv.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.symm_apply_eq`：symm_apply_eq {x : α} {y : β} (hx : x in e.s
ource) (hy : y in e.target) : e.symm y = x ↔ y = e x
-/
theorem symm_apply_eq (f : Equidecomp X G) {x y} (hx : x ∈ f.toPartialEquiv.target)
    (hy : y ∈ f.toPartialEquiv.source) : f.symm x = y ↔ x = f y :=
  f.toPartialEquiv.symm_apply_eq hy hx
/-
**Equidecomp.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp`。
形式化陈述：eq_symm_apply (f : Equidecomp X G) {x y} (hx : x in f.toPartialEquiv.targe
t) (hy : y in f.toPartialEquiv.source) : y = f.symm x ↔ f y = x
参数：f : Equidecomp X G；hx : x in f.toPartialEquiv.target；hy : y in f.toPartialEqu
iv.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.eq_symm_apply`：eq_symm_apply {x : α} {y : β} (hx : x in e.s
ource) (hy : y in e.target) : x = e.symm y ↔ e x = y
-/
theorem eq_symm_apply (f : Equidecomp X G) {x y} (hx : x ∈ f.toPartialEquiv.target)
    (hy : y ∈ f.toPartialEquiv.source) : y = f.symm x ↔ f y = x :=
  f.toPartialEquiv.eq_symm_apply hy hx
/-
**Equidecomp.symm_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp`。
形式化陈述：symm_involutive : Function.Involutive (symm : Equidecomp X G -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equidecomp.symm_symm`：symm_symm (f : Equidecomp X G) : f.symm.symm = f
-/
theorem symm_involutive : Function.Involutive (symm : Equidecomp X G → _) := symm_symm
/-
**Equidecomp.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp`。
形式化陈述：symm_bijective : Function.Bijective (symm : Equidecomp X G -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.bijective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Bijective f
· 使用定理 `Equidecomp.symm_involutive`：symm_involutive : Function.Involutive (symm 
: Equidecomp X G -> _)
-/
theorem symm_bijective : Function.Bijective (symm : Equidecomp X G → _) := symm_involutive.bijective

@[simp]
/-
**Equidecomp.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp`。
形式化陈述：refl_symm : (refl X G).symm = refl X G
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm : (refl X G).symm = refl X G := rfl

@[simp]
/-
**Equidecomp.restr_refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equidecomp`。
形式化陈述：restr_refl_symm (A : Set X) : ((Equidecomp.refl X G).restr A).symm = (Equi
decomp.refl X G).restr A
参数：A : Set X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restr_refl_symm (A : Set X) :
    ((Equidecomp.refl X G).restr A).symm = (Equidecomp.refl X G).restr A := rfl

end Group

end Equidecomp

