/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Shrink
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Finite.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The Hales-Jewett theorem

We prove the Hales-Jewett theorem. We deduce Van der Waerden's theorem and the multidimensional
Hales-Jewett theorem as corollaries.

The Hales-Jewett theorem is a result in Ramsey theory dealing with *combinatorial lines*. Given
an 'alphabet' `α : Type*` and `a b : α`, an example of a combinatorial line in `α^5` is
`{ (a, x, x, b, x) | x : α }`. See `Combinatorics.Line` for a precise general definition. The
Hales-Jewett theorem states that for any fixed finite types `α` and `κ`, there exists a (potentially
huge) finite type `ι` such that whenever `ι → α` is `κ`-colored (i.e. for any coloring
`C : (ι → α) → κ`), there exists a monochromatic line. We prove the Hales-Jewett theorem using
the idea of *color focusing* and a *product argument*. See the proof of
`Combinatorics.Line.exists_mono_in_high_dimension'` for details.

*Combinatorial subspaces* are higher-dimensional analogues of combinatorial lines. See
`Combinatorics.Subspace`. The multidimensional Hales-Jewett theorem generalises the statement above
from combinatorial lines to combinatorial subspaces of a fixed dimension.

The version of Van der Waerden's theorem in this file states that whenever a commutative monoid `M`
is finitely colored and `S` is a finite subset, there exists a monochromatic homothetic copy of `S`.
This follows from the Hales-Jewett theorem by considering the map `(ι → S) → M` sending `v`
to `∑ i : ι, v i`, which sends a combinatorial line to a homothetic copy of `S`.

## Main results

- `Combinatorics.Line.exists_mono_in_high_dimension`: The Hales-Jewett theorem.
- `Combinatorics.Subspace.exists_mono_in_high_dimension`: The multidimensional Hales-Jewett theorem.
- `Combinatorics.exists_mono_homothetic_copy`: A generalization of Van der Waerden's theorem.

## Implementation details

For convenience, we work directly with finite types instead of natural numbers. That is, we write
`α, ι, κ` for (finite) types where one might traditionally use natural numbers `n, H, c`. This
allows us to work directly with `α`, `Option α`, `(ι → α) → κ`, and `ι ⊕ ι'` instead of `Fin n`,
`Fin (n+1)`, `Fin (c^(n^H))`, and `Fin (H + H')`.

## TODO

- Prove a finitary version of Van der Waerden's theorem (either by compactness or by modifying the
  current proof).

- One could reformulate the proof of Hales-Jewett to give explicit upper bounds on the number of
  coordinates needed.

## Tags

combinatorial line, Ramsey theory, arithmetic progression

### References

* https://en.wikipedia.org/wiki/Hales%E2%80%93Jewett_theorem

-/

@[expose] public section

open Function
open scoped Finset

universe u v
variable {η α ι κ : Type*}

namespace Combinatorics

/-- The type of combinatorial subspaces. A subspace `l : Subspace η α ι` in the hypercube `ι → α`
defines a function `(η → α) → ι → α` from `η → α` to the hypercube, such that for each coordinate
`i : ι` and direction `e : η`, the function `fun x ↦ l x i` is either `fun x ↦ x e` for some
direction `e : η` or constant. We require subspaces to be non-degenerate in the sense that, for
every `e : η`, `fun x ↦ l x i` is `fun x ↦ x e` for at least one `i`.

Formally, a subspace is represented by a word `l.idxFun : ι → α ⊕ η` which says whether
`fun x ↦ l x i` is `fun x ↦ x e` (corresponding to `l.idxFun i = Sum.inr e`) or constantly `a`
(corresponding to `l.idxFun i = Sum.inl a`).

When `α` has size `1` there can be many elements of `Subspace η α ι` defining the same function. -/
@[ext]
/-
**Combinatorics.Subspace** 是 Mathlib 中的一个归纳类型，位于命名空间 `Combinatorics`。
形式化陈述：Type u_5 → Type u_6 → Type u_7 → Type (max (max u_5 u_6) u_7)
参数：max (max u_5 u_6) u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of combinatorial subspaces. A subspace `l : Subspace η α ι` in the hype
rcube `ι → α`
defines a function `(η → α) → ι → α` from `η → α` to the hypercube, such that fo
r each coordinate
`i : ι` and direction `e : η`, the function `fun x ↦ l x i` is either `fun x ↦ x
 e` for some
direction `e : η` or constant. We require subspaces to be non-degenerate in the 
sense that, for
every `e : η`, `fun x ↦ l x i` is `fun x ↦ x e` for at least one `i`.

Formally, a subspace is represented by a word `l.idxFun : ι → α ⊕ η` which says 
whether
`fun x ↦ l x i` is `fun x ↦ x e` (corresponding to `l.idxFun i = Sum.inr e`) or 
constantly `a`
(corresponding to `l.idxFun i = Sum.inl a`).

When `α` has size `1` there can be many elements of `Subspace η α ι` defining th
e same function.
-/
structure Subspace (η α ι : Type*) where
  /-- The word representing a combinatorial subspace. `l.idxfun i = Sum.inr e` means that
  `l x i = x e` for all `x` and `l.idxfun i = some a` means that `l x i = a` for all `x`. -/
  idxFun : ι → α ⊕ η
  /-- We require combinatorial subspaces to be nontrivial in the sense that `fun x ↦ l x i` is
  `fun x ↦ x e` for at least one coordinate `i`. -/
  proper : ∀ e, ∃ i, idxFun i = Sum.inr e

namespace Subspace
variable {η α ι κ : Type*} {l : Subspace η α ι} {x : η → α} {i : ι} {a : α} {e : η}

/-- The combinatorial subspace corresponding to the identity embedding `(ι → α) → (ι → α)`. -/
/-
**Combinatorics.Subspace.** 是 Mathlib 中的一个实例，位于命名空间 `Combinatorics.Subspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The combinatorial subspace corresponding to the identity embedding `(ι → α) → (ι
 → α)`.
-/
instance : Inhabited (Subspace ι α ι) := ⟨⟨Sum.inr, fun i ↦ ⟨i, rfl⟩⟩⟩

/-- Consider a subspace `l : Subspace η α ι` as a function `(η → α) → ι → α`. -/
/-
**Combinatorics.Subspace.toFun** 是 Mathlib 中的一个定义，位于命名空间 `Combinatorics.Subspace
`。
形式化陈述：{η : Type u_5} → {α : Type u_6} → {ι : Type u_7} → Combinatorics.Subspace 
η α ι → (η → α) → ι → α
参数：η → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider a subspace `l : Subspace η α ι` as a function `(η → α) → ι → α`.
-/
@[coe] def toFun (l : Subspace η α ι) (x : η → α) (i : ι) : α := (l.idxFun i).elim id x
/-
**Combinatorics.Subspace.instCoeFun** 是 Mathlib 中的一个实例，位于命名空间 `Combinatorics.Sub
space`。
形式化陈述：instCoeFun : CoeFun (Subspace η α ι) (fun _ => (η -> α) -> ι -> α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider a subspace `l : Subspace η α ι` as a function `(η → α) → ι → α`.
-/
instance instCoeFun : CoeFun (Subspace η α ι) (fun _ ↦ (η → α) → ι → α) := ⟨toFun⟩
/-
**Combinatorics.Subspace.coe_apply** 是 Mathlib 中的一个引理，位于命名空间 `Combinatorics.Subs
pace`。
形式化陈述：coe_apply (l : Subspace η α ι) (x : η -> α) (i : ι) : l x i = (l.idxFun i)
.elim id x
参数：l : Subspace η α ι；x : η -> α；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_apply (l : Subspace η α ι) (x : η → α) (i : ι) : l x i = (l.idxFun i).elim id x := rfl

-- Note: This is not made a `FunLike` instance to avoid having two syntactically different coercions
/-
**Combinatorics.Subspace.coe_injective** 是 Mathlib 中的一个引理，位于命名空间 `Combinatorics.
Subspace`。
形式化陈述：coe_injective [Nontrivial α] : Injective ((⇑) : Subspace η α ι -> (η -> α)
 -> ι -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Combinatorics.Subspace.ext`：∀ {η : Type u_5} {α : Type u_6} {ι : Type u_
7} {x y : Combinatorics.Subspace η α ι}, x.idxFun = y.idxFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
lemma coe_injective [Nontrivial α] : Injective ((⇑) : Subspace η α ι → (η → α) → ι → α) := by
  classical
  rintro l m hlm
  ext i
  simp only [funext_iff] at hlm
  cases hl : idxFun l i with
  | inl a =>
    obtain ⟨b, hba⟩ := exists_ne a
    cases hm : idxFun m i <;> simpa [hl, hm, hba.symm, coe_apply] using hlm (const _ b) i
  | inr e =>
    cases hm : idxFun m i with
    | inl a =>
      obtain ⟨b, hba⟩ := exists_ne a
      simpa [hl, hm, hba, coe_apply] using hlm (const _ b) i
    | inr f =>
      obtain ⟨a, b, hab⟩ := exists_pair_ne α
      simp only [Sum.inr.injEq]
      by_contra! hef
      simpa [hl, hm, hef, hab, coe_apply] using hlm (Function.update (const _ a) f b) i
/-
**Combinatorics.Subspace.apply_def** 是 Mathlib 中的一个引理，位于命名空间 `Combinatorics.Subs
pace`。
形式化陈述：apply_def (l : Subspace η α ι) (x : η -> α) (i : ι) : l x i = (l.idxFun i)
.elim id x
参数：l : Subspace η α ι；x : η -> α；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma apply_def (l : Subspace η α ι) (x : η → α) (i : ι) : l x i = (l.idxFun i).elim id x := rfl
/-
**Combinatorics.Subspace.apply_inl** 是 Mathlib 中的一个引理，位于命名空间 `Combinatorics.Subs
pace`。
形式化陈述：apply_inl (h : l.idxFun i = Sum.inl a) : l x i = a
参数：h : l.idxFun i = Sum.inl a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma apply_inl (h : l.idxFun i = Sum.inl a) : l x i = a := by simp [apply_def, h]
/-
**Combinatorics.Subspace.apply_inr** 是 Mathlib 中的一个引理，位于命名空间 `Combinatorics.Subs
pace`。
形式化陈述：apply_inr (h : l.idxFun i = Sum.inr e) : l x i = x e
参数：h : l.idxFun i = Sum.inr e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma apply_inr (h : l.idxFun i = Sum.inr e) : l x i = x e := by simp [apply_def, h]

/-- Given a coloring `C` of `ι → α` and a combinatorial subspace `l` of `ι → α`, `l.IsMono C`
means that `l` is monochromatic with regard to `C`. -/
/-
**Combinatorics.Subspace.IsMono** 是 Mathlib 中的一个定义，位于命名空间 `Combinatorics.Subspac
e`。
形式化陈述：IsMono (C : (ι -> α) -> κ) (l : Subspace η α ι) : Prop
参数：C : (ι -> α) -> κ；l : Subspace η α ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a coloring `C` of `ι → α` and a combinatorial subspace `l` of `ι → α`, `l.
IsMono C`
means that `l` is monochromatic with regard to `C`.
-/
def IsMono (C : (ι → α) → κ) (l : Subspace η α ι) : Prop := ∃ c, ∀ x, C (l x) = c

variable {η' α' ι' : Type*}

/-- Change the index types of a subspace. -/
/-
**Combinatorics.Subspace.reindex** 是 Mathlib 中的一个定义，位于命名空间 `Combinatorics.Subspa
ce`。
形式化陈述：reindex (l : Subspace η α ι) (eη : η ≃ η') (eα : α ≃ α') (eι : ι ≃ ι') : S
ubspace η' α' ι' where idxFun i
参数：l : Subspace η α ι；eη : η ≃ η'；eα : α ≃ α'；eι : ι ≃ ι'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Change the index types of a subspace.
-/
def reindex (l : Subspace η α ι) (eη : η ≃ η') (eα : α ≃ α') (eι : ι ≃ ι') : Subspace η' α' ι' where
  idxFun i := (l.idxFun <| eι.symm i).map eα eη
  proper e := (eι.exists_congr fun i ↦ by cases h : idxFun l i <;>
    simp [*, Equiv.eq_symm_apply]).1 <| l.proper <| eη.symm e
/-
**Combinatorics.Subspace.reindex_apply** 是 Mathlib 中的一个定理，位于命名空间 `Combinatorics.
Subspace`。
形式化陈述：∀ {η : Type u_5} {α : Type u_6} {ι : Type u_7} {η' : Type u_9} {α' : Type 
u_10} {ι' : Type u_11}   (l : Combinatorics.Subspace η α ι) (eη : η ≃ η') (eα : 
α ≃ α') (eι : ι ≃ ι') (x : η' → α') (i : ι'),   ↑(l.reindex eη eα eι) x i = eα (
↑l (⇑eα.symm ∘ x ∘ ⇑eη) (eι.symm i))
参数：l : Combinatorics.Subspace η α ι；eη : η ≃ η'；eα : α ≃ α'；eι : ι ≃ ι'；x : η' →
 α'；i : ι'；l.reindex eη eα eι；↑l (⇑eα.symm ∘ x ∘ ⇑eη) (eι.symm i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
@[simp] lemma reindex_apply (l : Subspace η α ι) (eη : η ≃ η') (eα : α ≃ α') (eι : ι ≃ ι') (x i) :
    l.reindex eη eα eι x i = eα (l (eα.symm ∘ x ∘ eη) <| eι.symm i) := by
  cases h : l.idxFun (eι.symm i) <;> simp [h, reindex, coe_apply]
/-
**Combinatorics.Subspace.reindex_isMono** 是 Mathlib 中的一个定理，位于命名空间 `Combinatorics
.Subspace`。
形式化陈述：∀ {η : Type u_5} {α : Type u_6} {ι : Type u_7} {κ : Type u_8} {l : Combina
torics.Subspace η α ι} {η' : Type u_9}   {α' : Type u_10} {ι' : Type u_11} {eη :
 η ≃ η'} {eα : α ≃ α'} {eι : ι ≃ ι'} {C : (ι' → α') → κ},   Combinatorics.Subspa
ce.IsMono C (l.reindex eη eα eι) ↔     Combinatorics.Subspace.IsMono (fun x => C
 (⇑eα ∘ x ∘ ⇑eι.symm)) l
参数：ι' → α'；l.reindex eη eα eι；fun x => C (⇑eα ∘ x ∘ ⇑eι.symm)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Combinatorics.Subspace.reindex_apply`：∀ {η : Type u_5} {α : Type u_6} {ι
 : Type u_7} {η' : Type u_9} {α' : Type u_10} {ι' : Type u_11}   (l : Combinator
ics.Subspace η α ι) (eη : …
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Equiv.forall_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∀ (a : α), p a) ↔ ∀ (b : β),
 q b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma reindex_isMono {eη : η ≃ η'} {eα : α ≃ α'} {eι : ι ≃ ι'} {C : (ι' → α') → κ} :
    (l.reindex eη eα eι).IsMono C ↔ l.IsMono fun x ↦ C <| eα ∘ x ∘ eι.symm := by
  simp only [IsMono, funext (reindex_apply _ _ _ _ _), coe_apply]
  exact exists_congr fun c ↦ (eη.arrowCongr eα).symm.forall_congr <| by aesop
/-
**Combinatorics.Subspace.IsMono.reindex** 是 Mathlib 中的一个定理，位于命名空间 `Combinatorics
.Subspace.IsMono`。
形式化陈述：∀ {η : Type u_5} {α : Type u_6} {ι : Type u_7} {κ : Type u_8} {l : Combina
torics.Subspace η α ι} {η' : Type u_9}   {α' : Type u_10} {ι' : Type u_11} {eη :
 η ≃ η'} {eα : α ≃ α'} {eι : ι ≃ ι'} {C : (ι → α) → κ},   Combinatorics.Subspace
.IsMono C l →     Combinatorics.Subspace.IsMono (fun x => C (⇑eα.symm ∘ x ∘ ⇑eι)
) (l.reindex eη eα eι)
参数：ι → α；fun x => C (⇑eα.symm ∘ x ∘ ⇑eι)；l.reindex eη eα eι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
-/
protected lemma IsMono.reindex {eη : η ≃ η'} {eα : α ≃ α'} {eι : ι ≃ ι'} {C : (ι → α) → κ}
    (hl : l.IsMono C) : (l.reindex eη eα eι).IsMono fun x ↦ C <| eα.symm ∘ x ∘ eι := by
  simp [reindex_isMono, Function.comp_assoc]; simpa [← Function.comp_assoc]

end Subspace

/-- The type of combinatorial lines. A line `l : Line α ι` in the hypercube `ι → α` defines a
function `α → ι → α` from `α` to the hypercube, such that for each coordinate `i : ι`, the function
`fun x ↦ l x i` is either `id` or constant. We require lines to be nontrivial in the sense that
`fun x ↦ l x i` is `id` for at least one `i`.

Formally, a line is represented by a word `l.idxFun : ι → Option α` which says whether
`fun x ↦ l x i` is `id` (corresponding to `l.idxFun i = none`) or constantly `y` (corresponding to
`l.idxFun i = some y`).

When `α` has size `1` there can be many elements of `Line α ι` defining the same function. -/
@[ext]
/-
**Combinatorics.Line** 是 Mathlib 中的一个归纳类型，位于命名空间 `Combinatorics`。
形式化陈述：Type u_5 → Type u_6 → Type (max u_5 u_6)
参数：max u_5 u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of combinatorial lines. A line `l : Line α ι` in the hypercube `ι → α` 
defines a
function `α → ι → α` from `α` to the hypercube, such that for each coordinate `i
 : ι`, the function
`fun x ↦ l x i` is either `id` or constant. We require lines to be nontrivial in
 the sense that
`fun x ↦ l x i` is `id` for at least one `i`.

Formally, a line is represented by a word `l.idxFun : ι → Option α` which says w
hether
`fun x ↦ l x i` is `id` (corresponding to `l.idxFun i = none`) or constantly `y`
 (corresponding to
`l.idxFun i = some y`).

When `α` has size `1` there can be many elements of `Line α ι` defining the same
 function.
-/
structure Line (α ι : Type*) where
  /-- The word representing a combinatorial line. `l.idxfun i = none` means that
  `l x i = x` for all `x` and `l.idxfun i = some y` means that `l x i = y`. -/
  idxFun : ι → Option α
  /-- We require combinatorial lines to be nontrivial in the sense that `fun x ↦ l x i` is `id` for
  at least one coordinate `i`. -/
  proper : ∃ i, idxFun i = none

namespace Line
variable {l : Line α ι} {i : ι} {a x : α}

/-- Consider a line `l : Line α ι` as a function `α → ι → α`. -/
/-
**Combinatorics.Line.toFun** 是 Mathlib 中的一个定义，位于命名空间 `Combinatorics.Line`。
形式化陈述：{α : Type u_2} → {ι : Type u_3} → Combinatorics.Line α ι → α → ι → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider a line `l : Line α ι` as a function `α → ι → α`.
-/
@[coe] def toFun (l : Line α ι) (x : α) (i : ι) : α := (l.idxFun i).getD x

-- This lets us treat a line `l : Line α ι` as a function `α → ι → α`.
/-
**Combinatorics.Line.instCoeFun** 是 Mathlib 中的一个实例，位于命名空间 `Combinatorics.Line`。
形式化陈述：instCoeFun : CoeFun (Line α ι) fun _ => α -> ι -> α
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoeFun : CoeFun (Line α ι) fun _ => α → ι → α := ⟨toFun⟩
/-
**Combinatorics.Line.coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `Combinatorics.Line`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_3} (l : Combinatorics.Line α ι) (x : α) (i : 
ι), ↑l x i = (l.idxFun i).getD x
参数：l : Combinatorics.Line α ι；x : α；i : ι；l.idxFun i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_apply (l : Line α ι) (x : α) (i : ι) : l x i = (l.idxFun i).getD x := rfl

-- Note: This is not made a `FunLike` instance to avoid having two syntactically different coercions
/-
**Combinatorics.Line.coe_injective** 是 Mathlib 中的一个引理，位于命名空间 `Combinatorics.Line
`。
形式化陈述：coe_injective [Nontrivial α] : Injective ((⇑) : Line α ι -> α -> ι -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Combinatorics.Line.ext`：∀ {α : Type u_5} {ι : Type u_6} {x y : Combinato
rics.Line α ι}, x.idxFun = y.idxFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
-/
lemma coe_injective [Nontrivial α] : Injective ((⇑) : Line α ι → α → ι → α) := by
  rintro l m hlm
  ext i a
  obtain ⟨b, hba⟩ := exists_ne a
  simp only [funext_iff] at hlm ⊢
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · cases hi : idxFun m i <;> simpa [@eq_comm _ a, hi, h, hba] using hlm b i
  · cases hi : idxFun l i <;> simpa [@eq_comm _ a, hi, h, hba] using hlm b i

/-- A line is monochromatic if all its points are the same color. -/
/-
**Combinatorics.Line.IsMono** 是 Mathlib 中的一个定义，位于命名空间 `Combinatorics.Line`。
形式化陈述：IsMono {α ι κ} (C : (ι -> α) -> κ) (l : Line α ι) : Prop
参数：C : (ι -> α) -> κ；l : Line α ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A line is monochromatic if all its points are the same color.
-/
def IsMono {α ι κ} (C : (ι → α) → κ) (l : Line α ι) : Prop :=
  ∃ c, ∀ x, C (l x) = c

/-- Consider a line as a one-dimensional subspace. -/
/-
**Combinatorics.Line.toSubspaceUnit** 是 Mathlib 中的一个定义，位于命名空间 `Combinatorics.Lin
e`。
形式化陈述：toSubspaceUnit (l : Line α ι) : Subspace Unit α ι where idxFun i
参数：l : Line α ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider a line as a one-dimensional subspace.
-/
def toSubspaceUnit (l : Line α ι) : Subspace Unit α ι where
  idxFun i := (l.idxFun i).elim (.inr ()) .inl
  proper _ := l.proper.imp fun i hi ↦ by simp [hi]
/-
**Combinatorics.Line.toSubspaceUnit_apply** 是 Mathlib 中的一个定理，位于命名空间 `Combinatori
cs.Line`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_3} (l : Combinatorics.Line α ι) (a : Unit → α
), ↑l.toSubspaceUnit a = ↑l (a ())
参数：l : Combinatorics.Line α ι；a : Unit → α；a ()。
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma toSubspaceUnit_apply (l : Line α ι) (a) : ⇑l.toSubspaceUnit a = l (a ()) := by
  ext i; cases h : l.idxFun i <;> simp [toSubspaceUnit, h, Subspace.coe_apply]
/-
**Combinatorics.Line.toSubspaceUnit_isMono** 是 Mathlib 中的一个定理，位于命名空间 `Combinator
ics.Line`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_3} {κ : Type u_4} {l : Combinatorics.Line α ι
} {C : (ι → α) → κ},   Combinatorics.Subspace.IsMono C l.toSubspaceUnit ↔ Combin
atorics.Line.IsMono C l
参数：ι → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Combinatorics.Line.toSubspaceUnit_apply`：∀ {α : Type u_2} {ι : Type u_3}
 (l : Combinatorics.Line α ι) (a : Unit → α), ↑l.toSubspaceUnit a = ↑l (a ())
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
-/
@[simp] lemma toSubspaceUnit_isMono {C : (ι → α) → κ} : l.toSubspaceUnit.IsMono C ↔ l.IsMono C := by
  simp only [Subspace.IsMono, toSubspaceUnit_apply, IsMono]
  exact exists_congr fun c ↦ ⟨fun h a ↦ h fun _ ↦ a, fun h a ↦ h _⟩

protected alias ⟨_, IsMono.toSubspaceUnit⟩ := toSubspaceUnit_isMono

/-- Consider a line in `ι → η → α` as a `η`-dimensional subspace in `ι × η → α`. -/
/-
**Combinatorics.Line.toSubspace** 是 Mathlib 中的一个定义，位于命名空间 `Combinatorics.Line`。
形式化陈述：toSubspace (l : Line (η -> α) ι) : Subspace η α (ι × η) where idxFun ie
参数：l : Line (η -> α) ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider a line in `ι → η → α` as a `η`-dimensional subspace in `ι × η → α`.
-/
def toSubspace (l : Line (η → α) ι) : Subspace η α (ι × η) where
  idxFun ie := (l.idxFun ie.1).elim (.inr ie.2) (fun f ↦ .inl <| f ie.2)
  proper e := let ⟨i, hi⟩ := l.proper; ⟨(i, e), by simp [hi]⟩
/-
**Combinatorics.Line.toSubspace_apply** 是 Mathlib 中的一个定理，位于命名空间 `Combinatorics.L
ine`。
形式化陈述：∀ {η : Type u_1} {α : Type u_2} {ι : Type u_3} (l : Combinatorics.Line (η 
→ α) ι) (a : η → α) (ie : ι × η),   ↑l.toSubspace a ie = ↑l a ie.1 ie.2
参数：l : Combinatorics.Line (η → α) ι；a : η → α；ie : ι × η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma toSubspace_apply (l : Line (η → α) ι) (a ie) :
    ⇑l.toSubspace a ie = l a ie.1 ie.2 := by
  cases h : l.idxFun ie.1 <;> simp [toSubspace, h, coe_apply, Subspace.coe_apply]
/-
**Combinatorics.Line.toSubspace_isMono** 是 Mathlib 中的一个定理，位于命名空间 `Combinatorics.
Line`。
形式化陈述：∀ {η : Type u_1} {α : Type u_2} {ι : Type u_3} {κ : Type u_4} {l : Combina
torics.Line (η → α) ι} {C : (ι × η → α) → κ},   Combinatorics.Subspace.IsMono C 
l.toSubspace ↔     Combinatorics.Line.IsMono       (fun x =>         C fun x_1 =
>           match x_1 with           | (i, e) => x i e)       l
参数：η → α；ι × η → α；fun x =>         C fun x_1 =>           match x_1 with       
    | (i, e) => x i e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Combinatorics.Line.toSubspace_apply`：∀ {η : Type u_1} {α : Type u_2} {ι 
: Type u_3} (l : Combinatorics.Line (η → α) ι) (a : η → α) (ie : ι × η),   ↑l.to
Subspace a ie = ↑l a ie.1…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toSubspace_isMono {l : Line (η → α) ι} {C : (ι × η → α) → κ} :
    l.toSubspace.IsMono C ↔ l.IsMono fun x : ι → η → α ↦ C fun (i, e) ↦ x i e := by
  simp [Subspace.IsMono, IsMono, funext (toSubspace_apply _ _)]

protected alias ⟨_, IsMono.toSubspace⟩ := toSubspace_isMono

/-- The diagonal line. It is the identity at every coordinate. -/
/-
**Combinatorics.Line.diagonal** 是 Mathlib 中的一个定义，位于命名空间 `Combinatorics.Line`。
形式化陈述：diagonal (α ι) [Nonempty ι] : Line α ι where idxFun _
参数：α ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagonal line. It is the identity at every coordinate.
-/
def diagonal (α ι) [Nonempty ι] : Line α ι where
  idxFun _ := none
  proper := ⟨Classical.arbitrary ι, rfl⟩
/-
**Combinatorics.Line.** 是 Mathlib 中的一个实例，位于命名空间 `Combinatorics.Line`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α ι) [Nonempty ι] : Inhabited (Line α ι) :=
  ⟨diagonal α ι⟩

/-- The type of lines that are only one color except possibly at their endpoints. -/
/-
**Combinatorics.Line.AlmostMono** 是 Mathlib 中的一个归纳类型，位于命名空间 `Combinatorics.Line`
。
形式化陈述：{α : Type u_5} → {ι : Type u_6} → {κ : Type u_7} → ((ι → Option α) → κ) → 
Type (max (max u_5 u_6) u_7)
参数：(ι → Option α) → κ；max (max u_5 u_6) u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of lines that are only one color except possibly at their endpoints.
-/
structure AlmostMono {α ι κ : Type*} (C : (ι → Option α) → κ) where
  /-- The underlying line of an almost monochromatic line, where the coordinate dimension `α` is
  extended by an additional symbol `none`, thought to be marking the endpoint of the line. -/
  line : Line (Option α) ι
  /-- The main color of an almost monochromatic line. -/
  color : κ
  /-- The proposition that the underlying line of an almost monochromatic line assumes its main
  color except possibly at the endpoints. -/
  has_color : ∀ x : α, C (line (some x)) = color
/-
**Combinatorics.Line.** 是 Mathlib 中的一个实例，位于命名空间 `Combinatorics.Line`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α ι κ : Type*} [Nonempty ι] [Inhabited κ] :
    Inhabited (AlmostMono fun _ : ι → Option α => (default : κ)) :=
  ⟨{  line := default
      color := default
      has_color := fun _ ↦ rfl}⟩

/-- The type of collections of lines such that
- each line is only one color except possibly at its endpoint
- the lines all have the same endpoint
- the colors of the lines are distinct.

Used in the proof `exists_mono_in_high_dimension`. -/
/-
**Combinatorics.Line.ColorFocused** 是 Mathlib 中的一个归纳类型，位于命名空间 `Combinatorics.Lin
e`。
形式化陈述：{α : Type u_5} → {ι : Type u_6} → {κ : Type u_7} → ((ι → Option α) → κ) → 
Type (max (max u_5 u_6) u_7)
参数：(ι → Option α) → κ；max (max u_5 u_6) u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of collections of lines such that
- each line is only one color except possibly at its endpoint
- the lines all have the same endpoint
- the colors of the lines are distinct.

Used in the proof `exists_mono_in_high_dimension`.
-/
structure ColorFocused {α ι κ : Type*} (C : (ι → Option α) → κ) where
  /-- The underlying multiset of almost monochromatic lines of a color-focused collection. -/
  lines : Multiset (AlmostMono C)
  /-- The common endpoint of the lines in the color-focused collection. -/
  focus : ι → Option α
  /-- The proposition that all lines in a color-focused collection have the same endpoint. -/
  is_focused : ∀ p ∈ lines, p.line none = focus
  /-- The proposition that all lines in a color-focused collection of lines have distinct colors. -/
  distinct_colors : (lines.map AlmostMono.color).Nodup
/-
**Combinatorics.Line.** 是 Mathlib 中的一个实例，位于命名空间 `Combinatorics.Line`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α ι κ} (C : (ι → Option α) → κ) : Inhabited (ColorFocused C) := by
  refine ⟨⟨0, fun _ => none, fun h => ?_, Multiset.nodup_zero⟩⟩
  simp only [Multiset.notMem_zero, IsEmpty.forall_iff]

/-- A function `f : α → α'` determines a function `line α ι → line α' ι`. For a coordinate `i`
`l.map f` is the identity at `i` if `l` is, and constantly `f y` if `l` is constantly `y` at `i`. -/
/-
**Combinatorics.Line.map** 是 Mathlib 中的一个定义，位于命名空间 `Combinatorics.Line`。
形式化陈述：map {α α' ι} (f : α -> α') (l : Line α ι) : Line α' ι where idxFun i
参数：f : α -> α'；l : Line α ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → α'` determines a function `line α ι → line α' ι`. For a coor
dinate `i`
`l.map f` is the identity at `i` if `l` is, and constantly `f y` if `l` is const
antly `y` at `i`.
-/
def map {α α' ι} (f : α → α') (l : Line α ι) : Line α' ι where
  idxFun i := (l.idxFun i).map f
  proper := ⟨l.proper.choose, by simp only [l.proper.choose_spec, Option.map_none]⟩

/-- A point in `ι → α` and a line in `ι' → α` determine a line in `ι ⊕ ι' → α`. -/
/-
**Combinatorics.Line.vertical** 是 Mathlib 中的一个定义，位于命名空间 `Combinatorics.Line`。
形式化陈述：vertical {α ι ι'} (v : ι -> α) (l : Line α ι') : Line α (ι oplus ι') where
 idxFun
参数：v : ι -> α；l : Line α ι'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A point in `ι → α` and a line in `ι' → α` determine a line in `ι ⊕ ι' → α`.
-/
def vertical {α ι ι'} (v : ι → α) (l : Line α ι') : Line α (ι ⊕ ι') where
  idxFun := Sum.elim (some ∘ v) l.idxFun
  proper := ⟨Sum.inr l.proper.choose, l.proper.choose_spec⟩

/-- A line in `ι → α` and a point in `ι' → α` determine a line in `ι ⊕ ι' → α`. -/
/-
**Combinatorics.Line.horizontal** 是 Mathlib 中的一个定义，位于命名空间 `Combinatorics.Line`。
形式化陈述：horizontal {α ι ι'} (l : Line α ι) (v : ι' -> α) : Line α (ι oplus ι') whe
re idxFun
参数：l : Line α ι；v : ι' -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A line in `ι → α` and a point in `ι' → α` determine a line in `ι ⊕ ι' → α`.
-/
def horizontal {α ι ι'} (l : Line α ι) (v : ι' → α) : Line α (ι ⊕ ι') where
  idxFun := Sum.elim l.idxFun (some ∘ v)
  proper := ⟨Sum.inl l.proper.choose, l.proper.choose_spec⟩

/-- One line in `ι → α` and one in `ι' → α` together determine a line in `ι ⊕ ι' → α`. -/
/-
**Combinatorics.Line.prod** 是 Mathlib 中的一个定义，位于命名空间 `Combinatorics.Line`。
形式化陈述：prod {α ι ι'} (l : Line α ι) (l' : Line α ι') : Line α (ι oplus ι') where 
idxFun
参数：l : Line α ι；l' : Line α ι'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One line in `ι → α` and one in `ι' → α` together determine a line in `ι ⊕ ι' → α
`.
-/
def prod {α ι ι'} (l : Line α ι) (l' : Line α ι') : Line α (ι ⊕ ι') where
  idxFun := Sum.elim l.idxFun l'.idxFun
  proper := ⟨Sum.inl l.proper.choose, l.proper.choose_spec⟩
/-
**Combinatorics.Line.apply_def** 是 Mathlib 中的一个定理，位于命名空间 `Combinatorics.Line`。
形式化陈述：apply_def (l : Line α ι) (x : α) : l x = fun i => (l.idxFun i).getD x
参数：l : Line α ι；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_def (l : Line α ι) (x : α) : l x = fun i => (l.idxFun i).getD x := rfl
/-
**Combinatorics.Line.apply_none** 是 Mathlib 中的一个定理，位于命名空间 `Combinatorics.Line`。
形式化陈述：apply_none {α ι} (l : Line α ι) (x : α) (i : ι) (h : l.idxFun i = none) : 
l x i = x
参数：l : Line α ι；x : α；i : ι；h : l.idxFun i = none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem apply_none {α ι} (l : Line α ι) (x : α) (i : ι) (h : l.idxFun i = none) : l x i = x := by
  simp only [Option.getD_none, h, l.apply_def]
/-
**Combinatorics.Line.apply_some** 是 Mathlib 中的一个引理，位于命名空间 `Combinatorics.Line`。
形式化陈述：apply_some (h : l.idxFun i = some a) : l x i = a
参数：h : l.idxFun i = some a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma apply_some (h : l.idxFun i = some a) : l x i = a := by simp [h]

@[simp]
/-
**Combinatorics.Line.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `Combinatorics.Line`。
形式化陈述：map_apply {α α' ι} (f : α -> α') (l : Line α ι) (x : α) : l.map f (f x) = 
f ∘ l x
参数：f : α -> α'；l : Line α ι；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.getD_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (x : α) (o 
: Option α), (Option.map f o).getD (f x) = f (o.getD x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_apply {α α' ι} (f : α → α') (l : Line α ι) (x : α) : l.map f (f x) = f ∘ l x := by
  simp only [Line.apply_def, Line.map, Option.getD_map, comp_def]

@[simp]
/-
**Combinatorics.Line.vertical_apply** 是 Mathlib 中的一个定理，位于命名空间 `Combinatorics.Lin
e`。
形式化陈述：vertical_apply {α ι ι'} (v : ι -> α) (l : Line α ι') (x : α) : l.vertical 
v x = Sum.elim v (l x)
参数：v : ι -> α；l : Line α ι'；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem vertical_apply {α ι ι'} (v : ι → α) (l : Line α ι') (x : α) :
    l.vertical v x = Sum.elim v (l x) := by
  funext i
  cases i <;> rfl

@[simp]
/-
**Combinatorics.Line.horizontal_apply** 是 Mathlib 中的一个定理，位于命名空间 `Combinatorics.L
ine`。
形式化陈述：horizontal_apply {α ι ι'} (l : Line α ι) (v : ι' -> α) (x : α) : l.horizon
tal v x = Sum.elim (l x) v
参数：l : Line α ι；v : ι' -> α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem horizontal_apply {α ι ι'} (l : Line α ι) (v : ι' → α) (x : α) :
    l.horizontal v x = Sum.elim (l x) v := by
  funext i
  cases i <;> rfl

@[simp]
/-
**Combinatorics.Line.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `Combinatorics.Line`。
形式化陈述：prod_apply {α ι ι'} (l : Line α ι) (l' : Line α ι') (x : α) : l.prod l' x 
= Sum.elim (l x) (l' x)
参数：l : Line α ι；l' : Line α ι'；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem prod_apply {α ι ι'} (l : Line α ι) (l' : Line α ι') (x : α) :
    l.prod l' x = Sum.elim (l x) (l' x) := by
  funext i
  cases i <;> rfl

@[simp]
/-
**Combinatorics.Line.diagonal_apply** 是 Mathlib 中的一个定理，位于命名空间 `Combinatorics.Lin
e`。
形式化陈述：diagonal_apply {α ι} [Nonempty ι] (x : α) : diagonal α ι x = fun _ => x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagonal_apply {α ι} [Nonempty ι] (x : α) : diagonal α ι x = fun _ => x := by
  ext; simp [diagonal]

/-- The **Hales-Jewett theorem**. This version has a restriction on universe levels which is
necessary for the proof. See `exists_mono_in_high_dimension` for a fully universe-polymorphic
version. -/
/-
**Combinatorics.Line.exists_mono_in_high_dimension'** 是 Mathlib 中的一个定理，位于命名空间 `C
ombinatorics.Line`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **Hales-Jewett theorem**. This version has a restriction on universe levels 
which is
necessary for the proof. See `exists_mono_in_high_dimension` for a fully univers
e-polymorphic
version.
-/
private theorem exists_mono_in_high_dimension' :
    ∀ (α : Type u) [Finite α] (κ : Type max v u) [Finite κ],
      ∃ (ι : Type) (_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Line α ι, l.IsMono C :=
-- The proof proceeds by induction on `α`.
  Finite.induction_empty_option
  (-- We have to show that the theorem is invariant under `α ≃ α'` for the induction to work.
  fun {α α'} e =>
    forall_imp fun κ =>
      forall_imp fun _ =>
        Exists.imp fun ι =>
          Exists.imp fun _ h C =>
            let ⟨l, c, lc⟩ := h fun v => C (e ∘ v)
            ⟨l.map e, c, e.forall_congr_right.mp fun x => by rw [← lc x, Line.map_apply]⟩)
  (by
    -- This deals with the degenerate case where `α` is empty.
    intro κ _
    by_cases h : Nonempty κ
    · refine ⟨Unit, inferInstance, fun C => ⟨default, Classical.arbitrary _, PEmpty.rec⟩⟩
    · exact ⟨Empty, inferInstance, fun C => (h ⟨C (Empty.rec)⟩).elim⟩)
  (by
    -- Now we have to show that the theorem holds for `Option α` if it holds for `α`.
    intro α _ ihα κ _
    cases nonempty_fintype κ
    -- Later we'll need `α` to be nonempty. So we first deal with the trivial case where `α` is
    -- empty.
    -- Then `Option α` has only one element, so any line is monochromatic.
    by_cases h : Nonempty α
    case neg =>
      refine ⟨Unit, inferInstance, fun C => ⟨diagonal _ Unit, C fun _ => none, ?_⟩⟩
      rintro (_ | ⟨a⟩)
      · rfl
      · exact (h ⟨a⟩).elim
    -- The key idea is to show that for every `r`, in high dimension we can either find
    -- `r` color focused lines or a monochromatic line.
    suffices key :
      ∀ r : ℕ,
        ∃ (ι : Type) (_ : Fintype ι),
          ∀ C : (ι → Option α) → κ,
            (∃ s : ColorFocused C, Multiset.card s.lines = r) ∨ ∃ l, IsMono C l by
      -- Given the key claim, we simply take `r = |κ| + 1`. We cannot have this many distinct colors
      -- so we must be in the second case, where there is a monochromatic line.
      obtain ⟨ι, _inst, hι⟩ := key (Fintype.card κ + 1)
      refine ⟨ι, _inst, fun C => (hι C).resolve_left ?_⟩
      rintro ⟨s, sr⟩
      apply Nat.not_succ_le_self (Fintype.card κ)
      rw [← Nat.add_one, ← sr, ← Multiset.card_map, ← Finset.card_mk]
      exact Finset.card_le_univ ⟨_, s.distinct_colors⟩
    -- We now prove the key claim, by induction on `r`.
    intro r
    induction r with
    -- The base case `r = 0` is trivial as the empty collection is color-focused.
    | zero => exact ⟨Empty, inferInstance, fun C => Or.inl ⟨default, Multiset.card_zero⟩⟩
    | succ r ihr =>
    -- Supposing the key claim holds for `r`, we need to show it for `r+1`. First pick a high
    -- enough dimension `ι` for `r`.
    obtain ⟨ι, _inst, hι⟩ := ihr
    -- Then since the theorem holds for `α` with any number of colors, pick a dimension `ι'` such
    -- that `ι' → α` always has a monochromatic line whenever it is `(ι → Option α) → κ`-colored.
    specialize ihα ((ι → Option α) → κ)
    obtain ⟨ι', _inst, hι'⟩ := ihα
    -- We claim that `ι ⊕ ι'` works for `Option α` and `κ`-coloring.
    refine ⟨ι ⊕ ι', inferInstance, ?_⟩
    intro C
    -- A `κ`-coloring of `ι ⊕ ι' → Option α` induces an `(ι → Option α) → κ`-coloring of `ι' → α`.
    specialize hι' fun v' v => C (Sum.elim v (some ∘ v'))
    -- By choice of `ι'` this coloring has a monochromatic line `l'` with color class `C'`, where
    -- `C'` is a `κ`-coloring of `ι → α`.
    obtain ⟨l', C', hl'⟩ := hι'
    -- If `C'` has a monochromatic line, then so does `C`. We use this in two places below.
    have mono_of_mono : (∃ l, IsMono C' l) → ∃ l, IsMono C l := by
      rintro ⟨l, c, hl⟩
      refine ⟨l.horizontal (some ∘ l' (Classical.arbitrary α)), c, fun x => ?_⟩
      rw [Line.horizontal_apply, ← hl, ← hl']
    -- By choice of `ι`, `C'` either has `r` color-focused lines or a monochromatic line.
    specialize hι C'
    rcases hι with (⟨s, sr⟩ | h)
    on_goal 2 => exact Or.inr (mono_of_mono h)
    -- Here we assume `C'` has `r` color focused lines. We split into cases depending on whether
    -- one of these `r` lines has the same color as the focus point.
    by_cases h : ∃ p ∈ s.lines, (p : AlmostMono _).color = C' s.focus
    -- If so then this is a `C'`-monochromatic line and we are done.
    · obtain ⟨p, p_mem, hp⟩ := h
      refine Or.inr (mono_of_mono ⟨p.line, p.color, ?_⟩)
      rintro (_ | _)
      · rw [hp, s.is_focused p p_mem]
      · apply p.has_color
    -- If not, we get `r+1` color focused lines by taking the product of the `r` lines with `l'`
    -- and adding to this the vertical line obtained by the focus point and `l`.
    refine Or.inl ⟨⟨(s.lines.map ?_).cons ⟨(l'.map some).vertical s.focus, C' s.focus, fun x => ?_⟩,
            Sum.elim s.focus (l'.map some none), ?_, ?_⟩, ?_⟩
    -- The product lines are almost monochromatic.
    · refine fun p => ⟨p.line.prod (l'.map some), p.color, fun x => ?_⟩
      rw [Line.prod_apply, Line.map_apply, ← p.has_color, ← congr_fun (hl' x)]
    -- The vertical line is almost monochromatic.
    · rw [vertical_apply, ← congr_fun (hl' x), Line.map_apply]
    -- Our `r+1` lines have the same endpoint.
    · simp_rw [Multiset.mem_cons, Multiset.mem_map]
      rintro _ (rfl | ⟨q, hq, rfl⟩)
      · simp only [vertical_apply]
      · simp only [prod_apply, s.is_focused q hq]
    -- Our `r+1` lines have distinct colors (this is why we needed to split into cases above).
    · rw [Multiset.map_cons, Multiset.map_map, Multiset.nodup_cons, Multiset.mem_map]
      exact ⟨h, s.distinct_colors⟩
    -- Finally, we really do have `r+1` lines!
    · rw [Multiset.card_cons, Multiset.card_map, sr])

/-- The **Hales-Jewett theorem**: For any finite types `α` and `κ`, there exists a finite type `ι`
such that whenever the hypercube `ι → α` is `κ`-colored, there is a monochromatic combinatorial
line. -/
/-
**Combinatorics.Line.exists_mono_in_high_dimension** 是 Mathlib 中的一个定理，位于命名空间 `Co
mbinatorics.Line`。
形式化陈述：exists_mono_in_high_dimension (α : Type u) [Finite α] (κ : Type v) [Finite
 κ] : exists (ι : Type) (_ : Fintype ι), forall C : (ι -> α) -> κ, exists l : Li
ne α ι, l.IsMono C
参数：α : Type u；κ : Type v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Combinatorics.HalesJewett.0.Combinatorics.Line.exists_m
ono_in_high_dimension'`：∀ (α : Type u) [Finite α] (κ : Type (max v u)) [Finite κ
],   ∃ ι x, ∀ (C : (ι → α) → κ), ∃ l, Combinatorics.Line.IsMono C l
· 使用定理 `instFiniteULift`：∀ {α : Type v} [Finite α], Finite (ULift.{u, v} α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)

--- 原说明 ---
The **Hales-Jewett theorem**: For any finite types `α` and `κ`, there exists a f
inite type `ι`
such that whenever the hypercube `ι → α` is `κ`-colored, there is a monochromati
c combinatorial
line.
-/
theorem exists_mono_in_high_dimension (α : Type u) [Finite α] (κ : Type v) [Finite κ] :
    ∃ (ι : Type) (_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Line α ι, l.IsMono C :=
  let ⟨ι, ιfin, hι⟩ := exists_mono_in_high_dimension'.{u, v} α (ULift.{u, v} κ)
  ⟨ι, ιfin, fun C =>
    let ⟨l, c, hc⟩ := hι (ULift.up ∘ C)
    ⟨l, c.down, fun x => by rw [← hc x, Function.comp_apply]⟩⟩

end Line

/-- A generalization of Van der Waerden's theorem: if `M` is a finitely colored commutative
monoid, and `S` is a finite subset, then there exists a monochromatic homothetic copy of `S`. -/
/-
**Combinatorics.exists_mono_homothetic_copy** 是 Mathlib 中的一个定理，位于命名空间 `Combinato
rics`。
形式化陈述：exists_mono_homothetic_copy {M κ : Type*} [AddCommMonoid M] (S : Finset M)
 [Finite κ] (C : M -> κ) : exists a > 0, exists (b : M) (c : κ), forall s in S, 
C (a • s + b) = c
参数：S : Finset M；C : M -> κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Combinatorics.Line.exists_mono_in_high_dimension`：exists_mono_in_high_di
mension (α : Type u) [Finite α] (κ : Type v) [Finite κ] : exists (ι : Type) (_ :
 Fintype ι), forall C : (ι -> α) -> κ,…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Combinatorics.Line.proper`：∀ {α : Type u_5} {ι : Type u_6} (self : Combi
natorics.Line α ι), ∃ i, self.idxFun i = none
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_add_sum_compl`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (s : Finset ι)   (f : ι
 → M), ∑ i ∈ s…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Combinatorics.Line.apply_none`：apply_none {α ι} (l : Line α ι) (x : α) (
i : ι) (h : l.idxFun i = none) : l x i = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.ne_none_iff_exists`：∀ {α : Type u_1} {o : Option α}, o ≠ none ↔ ∃
 x, some x = o
· 使用定理 `Finset.compl_filter`：compl_filter (p : α -> Prop) [DecidablePred p] [for
all x, Decidable ¬p x] : (univ.filter p)ᶜ = univ.filter fun x => ¬p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A generalization of Van der Waerden's theorem: if `M` is a finitely colored comm
utative
monoid, and `S` is a finite subset, then there exists a monochromatic homothetic
 copy of `S`.
-/
theorem exists_mono_homothetic_copy {M κ : Type*} [AddCommMonoid M] (S : Finset M) [Finite κ]
    (C : M → κ) : ∃ a > 0, ∃ (b : M) (c : κ), ∀ s ∈ S, C (a • s + b) = c := by
  classical
  obtain ⟨ι, _inst, hι⟩ := Line.exists_mono_in_high_dimension S κ
  specialize hι fun v => C <| ∑ i, v i
  obtain ⟨l, c, hl⟩ := hι
  set s : Finset ι := {i | l.idxFun i = none} with hs
  refine ⟨#s, Finset.card_pos.mpr ⟨l.proper.choose, ?_⟩, ∑ i ∈ sᶜ, ((l.idxFun i).map ?_).getD 0,
    c, ?_⟩
  · rw [hs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, l.proper.choose_spec⟩
  · exact fun m => m
  intro x xs
  rw [← hl ⟨x, xs⟩]
  clear hl; congr
  rw [← Finset.sum_add_sum_compl s]
  congr 1
  · rw [← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hs, Finset.mem_filter] at hi
    rw [l.apply_none _ _ hi.right, Subtype.coe_mk]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [hs, Finset.compl_filter, Finset.mem_filter] at hi
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hi.right
    simp [← hy, Option.map_some, Option.getD]

namespace Subspace

/-- The **multidimensional Hales-Jewett theorem**, aka **extended Hales-Jewett theorem**: For any
finite types `η`, `α` and `κ`, there exists a finite type `ι` such that whenever the hypercube
`ι → α` is `κ`-colored, there is a monochromatic combinatorial subspace of dimension `η`. -/
/-
**Combinatorics.Subspace.exists_mono_in_high_dimension** 是 Mathlib 中的一个定理，位于命名空间
 `Combinatorics.Subspace`。
形式化陈述：exists_mono_in_high_dimension (α κ η) [Finite α] [Finite κ] [Finite η] : e
xists (ι : Type) (_ : Fintype ι), forall C : (ι -> α) -> κ, exists l : Subspace 
η α ι, l.IsMono C
参数：α κ η。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Countable.toSmall`：∀ (α : Type v) [Countable α], Small.{w, v} α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Combinatorics.Line.exists_mono_in_high_dimension`：exists_mono_in_high_di
mension (α : Type u) [Finite α] (κ : Type v) [Finite κ] : exists (ι : Type) (_ :
 Fintype ι), forall C : (ι -> α) -> κ,…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Combinatorics.Subspace.IsMono.reindex`：∀ {η : Type u_5} {α : Type u_6} {
ι : Type u_7} {κ : Type u_8} {l : Combinatorics.Subspace η α ι} {η' : Type u_9} 
  {α' : Type u_10} {ι' : Ty…
· 使用定理 `Combinatorics.Line.IsMono.toSubspace`：∀ {η : Type u_1} {α : Type u_2} {ι
 : Type u_3} {κ : Type u_4} {l : Combinatorics.Line (η → α) ι} {C : (ι × η → α) 
→ κ},   Combinatorics.Line…

--- 原说明 ---
The **multidimensional Hales-Jewett theorem**, aka **extended Hales-Jewett theor
em**: For any
finite types `η`, `α` and `κ`, there exists a finite type `ι` such that whenever
 the hypercube
`ι → α` is `κ`-colored, there is a monochromatic combinatorial subspace of dimen
sion `η`.
-/
theorem exists_mono_in_high_dimension (α κ η) [Finite α] [Finite κ] [Finite η] :
    ∃ (ι : Type) (_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Subspace η α ι, l.IsMono C := by
  cases nonempty_fintype η
  obtain ⟨ι, _, hι⟩ := Line.exists_mono_in_high_dimension (Shrink.{0} η → α) κ
  refine ⟨ι × Shrink η, inferInstance, fun C ↦ ?_⟩
  obtain ⟨l, hl⟩ := hι fun x ↦ C fun (i, e) ↦ x i e
  refine ⟨l.toSubspace.reindex (equivShrink.{0} η).symm (Equiv.refl _) (Equiv.refl _), ?_⟩
  convert! hl.toSubspace.reindex
  simp

/-- A variant of the **extended Hales-Jewett theorem** `exists_mono_in_high_dimension` where the
returned type is some `Fin n` instead of a general fintype. -/
/-
**Combinatorics.Subspace.exists_mono_in_high_dimension_fin** 是 Mathlib 中的一个定理，位于
命名空间 `Combinatorics.Subspace`。
形式化陈述：exists_mono_in_high_dimension_fin (α κ η) [Finite α] [Finite κ] [Finite η]
 : exists n, forall C : (Fin n -> α) -> κ, exists l : Subspace η α (Fin n), l.Is
Mono C
参数：α κ η。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Combinatorics.Subspace.exists_mono_in_high_dimension`：exists_mono_in_hig
h_dimension (α κ η) [Finite α] [Finite κ] [Finite η] : exists (ι : Type) (_ : Fi
ntype ι), forall C : (ι -> α) -> κ, exists…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Combinatorics.Subspace.proper`：∀ {η : Type u_5} {α : Type u_6} {ι : Type
 u_7} (self : Combinatorics.Subspace η α ι) (e : η),   ∃ i, self.idxFun i = Sum.
inr e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x

--- 原说明 ---
A variant of the **extended Hales-Jewett theorem** `exists_mono_in_high_dimensio
n` where the
returned type is some `Fin n` instead of a general fintype.
-/
theorem exists_mono_in_high_dimension_fin (α κ η) [Finite α] [Finite κ] [Finite η] :
    ∃ n, ∀ C : (Fin n → α) → κ, ∃ l : Subspace η α (Fin n), l.IsMono C := by
  obtain ⟨ι, ιfin, hι⟩ := exists_mono_in_high_dimension α κ η
  refine ⟨Fintype.card ι, fun C ↦ ?_⟩
  obtain ⟨l, c, cl⟩ := hι fun v ↦ C (v ∘ (Fintype.equivFin _).symm)
  refine ⟨⟨l.idxFun ∘ (Fintype.equivFin _).symm, fun e ↦ ?_⟩, c, cl⟩
  obtain ⟨i, hi⟩ := l.proper e
  use Fintype.equivFin _ i
  simpa using hi

end Subspace
end Combinatorics

