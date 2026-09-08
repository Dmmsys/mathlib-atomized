/-
Copyright (c) 2020 Kexing Ying and Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Kevin Buzzard, Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Algebra.Group.Support
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Notation.FiniteSupport
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Set.Finite.Lattice

import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Module.End
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite products and sums over types and sets

We define products and sums over types and subsets of types, with no finiteness hypotheses.
All infinite products and sums are defined to be junk values (i.e. one or zero).
This approach is sometimes easier to use than `Finset.sum`,
when issues arise with `Finset` and `Fintype` being data.

## Main definitions

We use the following variables:

* `α`, `β` - types with no structure;
* `s`, `t` - sets
* `M`, `N` - additive or multiplicative commutative monoids
* `f`, `g` - functions

Definitions in this file:

* `finsum f : M` : the sum of `f x` as `x` ranges over the support of `f`, if it's finite.
  Zero otherwise.

* `finprod f : M` : the product of `f x` as `x` ranges over the multiplicative support of `f`, if
  it's finite. One otherwise.

## Notation

* `∑ᶠ i, f i` and `∑ᶠ i : α, f i` for `finsum f`

* `∏ᶠ i, f i` and `∏ᶠ i : α, f i` for `finprod f`

This notation works for functions `f : p → M`, where `p : Prop`, so the following works:

* `∑ᶠ i ∈ s, f i`, where `f : α → M`, `s : Set α` : sum over the set `s`;
* `∑ᶠ n < 5, f n`, where `f : ℕ → M` : same as `f 0 + f 1 + f 2 + f 3 + f 4`;
* `∏ᶠ (n >= -2) (hn : n < 3), f n`, where `f : ℤ → M` : same as `f (-2) * f (-1) * f 0 * f 1 * f 2`.

## Implementation notes

`finsum` and `finprod` is "yet another way of doing finite sums and products in Lean". However
experiments in the wild (e.g. with matroids) indicate that it is a helpful approach in settings
where the user is not interested in computability and wants to do reasoning without running into
typeclass diamonds caused by the constructive finiteness used in definitions such as `Finset` and
`Fintype`. By sticking solely to `Set.Finite` we avoid these problems. We are aware that there are
other solutions but for beginner mathematicians this approach is easier in practice.

Another application is the construction of a partition of unity from a collection of “bump”
functions. In this case the finite set depends on the point and it's convenient to have a definition
that does not mention the set explicitly.

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

We did not add `IsFinite (X : Type) : Prop`, because it is simply `Nonempty (Fintype X)`.

## Tags

finsum, finprod, finite sum, finite product
-/

@[expose] public section


open Function Set

/-!
### Definition and relation to `Finset.sum` and `Finset.prod`
-/

section sort

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

section

/- Note: we use classical logic only for these definitions, to ensure that we do not write lemmas
with `Classical.dec` in their statement. -/

open scoped Classical in
/-- Sum of `f x` as `x` ranges over the elements of the support of `f`, if it's finite. Zero
otherwise. -/
noncomputable irreducible_def finsum (lemma := finsum_def') [AddCommMonoid M] (f : α → M) : M :=
  if h : HasFiniteSupport (f ∘ PLift.down) then ∑ i ∈ h.toFinset, f i.down else 0

open scoped Classical in
/-- Product of `f x` as `x` ranges over the elements of the multiplicative support of `f`, if it's
finite. One otherwise. -/
@[to_additive existing]
noncomputable irreducible_def finprod (lemma := finprod_def') (f : α → M) : M :=
  if h : HasFiniteMulSupport (f ∘ PLift.down) then ∏ i ∈ h.toFinset, f i.down else 1

attribute [to_additive existing] finprod_def'

end

open Batteries.ExtendedBinder

/-- `∑ᶠ x, f x` is notation for `finsum f`. It is the sum of `f x`, where `x` ranges over the
support of `f`, if it's finite, zero otherwise. Taking the sum over multiple arguments or
conditions is possible, e.g. `∏ᶠ (x) (y), f x y` and `∏ᶠ (x) (h: x ∈ s), f x` -/
notation3"∑ᶠ " (...) ", " r:67:(scoped f => finsum f) => r

/-- `∏ᶠ x, f x` is notation for `finprod f`. It is the product of `f x`, where `x` ranges over the
multiplicative support of `f`, if it's finite, one otherwise. Taking the product over multiple
arguments or conditions is possible, e.g. `∏ᶠ (x) (y), f x y` and `∏ᶠ (x) (h: x ∈ s), f x` -/
notation3"∏ᶠ " (...) ", " r:67:(scoped f => finprod f) => r

-- Porting note: The following ports the lean3 notation for this file, but is currently very fickle.

-- syntax (name := bigfinsum) "∑ᶠ" extBinders ", " term:67 : term
-- macro_rules (kind := bigfinsum)
--   | `(∑ᶠ $x:ident, $p) => `(finsum (fun $x:ident ↦ $p))
--   | `(∑ᶠ $x:ident : $t, $p) => `(finsum (fun $x:ident : $t ↦ $p))
--   | `(∑ᶠ $x:ident $b:binderPred, $p) =>
--     `(finsum fun $x => (finsum (α := satisfies_binder_pred% $x $b) (fun _ => $p)))

--   | `(∑ᶠ ($x:ident) ($h:ident : $t), $p) =>
--       `(finsum fun ($x) => finsum (α := $t) (fun $h => $p))
--   | `(∑ᶠ ($x:ident : $_) ($h:ident : $t), $p) =>
--       `(finsum fun ($x) => finsum (α := $t) (fun $h => $p))

--   | `(∑ᶠ ($x:ident) ($y:ident), $p) =>
--       `(finsum fun $x => (finsum fun $y => $p))
--   | `(∑ᶠ ($x:ident) ($y:ident) ($h:ident : $t), $p) =>
--       `(finsum fun $x => (finsum fun $y => (finsum (α := $t) fun $h => $p)))

--   | `(∑ᶠ ($x:ident) ($y:ident) ($z:ident), $p) =>
--       `(finsum fun $x => (finsum fun $y => (finsum fun $z => $p)))
--   | `(∑ᶠ ($x:ident) ($y:ident) ($z:ident) ($h:ident : $t), $p) =>
--       `(finsum fun $x => (finsum fun $y => (finsum fun $z => (finsum (α := $t) fun $h => $p))))
--
--
-- syntax (name := bigfinprod) "∏ᶠ " extBinders ", " term:67 : term
-- macro_rules (kind := bigfinprod)
--   | `(∏ᶠ $x:ident, $p) => `(finprod (fun $x:ident ↦ $p))
--   | `(∏ᶠ $x:ident : $t, $p) => `(finprod (fun $x:ident : $t ↦ $p))
--   | `(∏ᶠ $x:ident $b:binderPred, $p) =>
--     `(finprod fun $x => (finprod (α := satisfies_binder_pred% $x $b) (fun _ => $p)))

--   | `(∏ᶠ ($x:ident) ($h:ident : $t), $p) =>
--       `(finprod fun ($x) => finprod (α := $t) (fun $h => $p))
--   | `(∏ᶠ ($x:ident : $_) ($h:ident : $t), $p) =>
--       `(finprod fun ($x) => finprod (α := $t) (fun $h => $p))

--   | `(∏ᶠ ($x:ident) ($y:ident), $p) =>
--       `(finprod fun $x => (finprod fun $y => $p))
--   | `(∏ᶠ ($x:ident) ($y:ident) ($h:ident : $t), $p) =>
--       `(finprod fun $x => (finprod fun $y => (finprod (α := $t) fun $h => $p)))

--   | `(∏ᶠ ($x:ident) ($y:ident) ($z:ident), $p) =>
--       `(finprod fun $x => (finprod fun $y => (finprod fun $z => $p)))
--   | `(∏ᶠ ($x:ident) ($y:ident) ($z:ident) ($h:ident : $t), $p) =>
--       `(finprod fun $x => (finprod fun $y => (finprod fun $z =>
--          (finprod (α := $t) fun $h => $p))))

@[to_additive]
/-
**finprod_eq_prod_plift_of_mulSupport_toFinset_subset** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：finprod_eq_prod_plift_of_mulSupport_toFinset_subset {f : α -> M} (hf : Has
FiniteMulSupport (f ∘ PLift.down)) {s : Finset (PLift α)} (hs : hf.toFinset subs
eteq s) : ∏ᶠ i, f i = ∏ i in s, f i.down
参数：hf : HasFiniteMulSupport (f ∘ PLift.down)；PLift α；hs : hf.toFinset subseteq s
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_def'`：∀ {M : Type u_7} {α : Sort u_8} [inst : CommMonoid M] (f :
 α → M),   finprod f = if h : Function.HasFiniteMulSupport (f ∘ PLift.down) then
 ∏…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用引理 `Function.notMem_mulSupport`：notMem_mulSupport : x ∉ mulSupport f ↔ f x =
 1
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
-/
theorem finprod_eq_prod_plift_of_mulSupport_toFinset_subset {f : α → M}
    (hf : HasFiniteMulSupport (f ∘ PLift.down)) {s : Finset (PLift α)} (hs : hf.toFinset ⊆ s) :
    ∏ᶠ i, f i = ∏ i ∈ s, f i.down := by
  rw [finprod, dif_pos hf]
  refine Finset.prod_subset hs fun x _ hxf => ?_
  rwa [hf.mem_toFinset, notMem_mulSupport] at hxf

@[to_additive]
/-
**finprod_eq_prod_plift_of_mulSupport_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_eq_prod_plift_of_mulSupport_subset {f : α -> M} {s : Finset (PLift
 α)} (hs : mulSupport (f ∘ PLift.down) subseteq s) : ∏ᶠ i, f i = ∏ i in s, f i.d
own
参数：PLift α；hs : mulSupport (f ∘ PLift.down) subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_eq_prod_plift_of_mulSupport_toFinset_subset`：finprod_eq_prod_pli
ft_of_mulSupport_toFinset_subset {f : α -> M} (hf : HasFiniteMulSupport (f ∘ PLi
ft.down)) {s : Finset (PLift α)} (hs : hf…
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
-/
theorem finprod_eq_prod_plift_of_mulSupport_subset {f : α → M} {s : Finset (PLift α)}
    (hs : mulSupport (f ∘ PLift.down) ⊆ s) : ∏ᶠ i, f i = ∏ i ∈ s, f i.down :=
  finprod_eq_prod_plift_of_mulSupport_toFinset_subset (s.finite_toSet.subset hs) fun x hx => by
    rw [Finite.mem_toFinset] at hx
    exact hs hx

@[to_additive (attr := simp)]
/-
**finprod_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_one : (∏ᶠ _ : α, (1 : M)) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.mulSupport_fun_one`：mulSupport_fun_one : mulSupport (fun _ => 1
 : ι -> M) = ∅
· 使用定理 `finprod_eq_prod_plift_of_mulSupport_subset`：finprod_eq_prod_plift_of_mul
Support_subset {f : α -> M} {s : Finset (PLift α)} (hs : mulSupport (f ∘ PLift.d
own) subseteq s) : ∏ᶠ i, f i = ∏…
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
-/
theorem finprod_one : (∏ᶠ _ : α, (1 : M)) = 1 := by
  have : (mulSupport fun x : PLift α => (fun _ => 1 : α → M) x.down) ⊆ (∅ : Finset (PLift α)) :=
    fun x h => by simp at h
  rw [finprod_eq_prod_plift_of_mulSupport_subset this, Finset.prod_empty]

@[to_additive]
/-
**finprod_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_of_isEmpty [IsEmpty α] (f : α -> M) : ∏ᶠ i, f i = 1
参数：f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_one`：finprod_one : (∏ᶠ _ : α, (1 : M)) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem finprod_of_isEmpty [IsEmpty α] (f : α → M) : ∏ᶠ i, f i = 1 := by
  rw [← finprod_one]
  congr
  simp [eq_iff_true_of_subsingleton]

@[to_additive (attr := simp)]
/-
**finprod_false** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_false (f : False -> M) : ∏ᶠ i, f i = 1
参数：f : False -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_of_isEmpty`：finprod_of_isEmpty [IsEmpty α] (f : α -> M) : ∏ᶠ i, 
f i = 1
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem finprod_false (f : False → M) : ∏ᶠ i, f i = 1 :=
  finprod_of_isEmpty _

@[to_additive]
/-
**finprod_eq_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_eq_single (f : α -> M) (a : α) (ha : forall x, x != a -> f x = 1) 
: ∏ᶠ x, f x = f a
参数：f : α -> M；a : α；ha : forall x, x != a -> f x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `finprod_eq_prod_plift_of_mulSupport_subset`：finprod_eq_prod_plift_of_mul
Support_subset {f : α -> M} {s : Finset (PLift α)} (hs : mulSupport (f ∘ PLift.d
own) subseteq s) : ∏ᶠ i, f i = ∏…
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
-/
theorem finprod_eq_single (f : α → M) (a : α) (ha : ∀ x, x ≠ a → f x = 1) :
    ∏ᶠ x, f x = f a := by
  have : mulSupport (f ∘ PLift.down) ⊆ ({PLift.up a} : Finset (PLift α)) := by
    intro x
    contrapose
    simpa [PLift.eq_up_iff_down_eq] using ha x.down
  rw [finprod_eq_prod_plift_of_mulSupport_subset this, Finset.prod_singleton]

@[to_additive]
/-
**finprod_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_unique [Unique α] (f : α -> M) : ∏ᶠ i, f i = f default
参数：f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_eq_single`：finprod_eq_single (f : α -> M) (a : α) (ha : forall x
, x != a -> f x = 1) : ∏ᶠ x, f x = f a
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
-/
theorem finprod_unique [Unique α] (f : α → M) : ∏ᶠ i, f i = f default :=
  finprod_eq_single f default fun _x hx => (hx <| Unique.eq_default _).elim

@[to_additive (attr := simp)]
/-
**finprod_true** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_true (f : True -> M) : ∏ᶠ i, f i = f trivial
参数：f : True -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_unique`：finprod_unique [Unique α] (f : α -> M) : ∏ᶠ i, f i = f d
efault
· 使用定理 `trivial`：True
-/
theorem finprod_true (f : True → M) : ∏ᶠ i, f i = f trivial :=
  @finprod_unique M True _ ⟨⟨trivial⟩, fun _ => rfl⟩ f

@[to_additive]
/-
**finprod_eq_dif** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_eq_dif {p : Prop} [Decidable p] (f : p -> M) : ∏ᶠ i, f i = if h : 
p then f h else 1
参数：f : p -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `finprod_unique`：finprod_unique [Unique α] (f : α -> M) : ∏ᶠ i, f i = f d
efault
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `finprod_of_isEmpty`：finprod_of_isEmpty [IsEmpty α] (f : α -> M) : ∏ᶠ i, 
f i = 1
-/
theorem finprod_eq_dif {p : Prop} [Decidable p] (f : p → M) :
    ∏ᶠ i, f i = if h : p then f h else 1 := by
  split_ifs with h
  · have : Unique p := ⟨⟨h⟩, fun _ => rfl⟩
    exact finprod_unique f
  · have : IsEmpty p := ⟨h⟩
    exact finprod_of_isEmpty f

@[to_additive]
/-
**finprod_eq_if** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_eq_if {p : Prop} [Decidable p] {x : M} : ∏ᶠ _ : p, x = if p then x
 else 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_eq_dif`：finprod_eq_dif {p : Prop} [Decidable p] (f : p -> M) : ∏
ᶠ i, f i = if h : p then f h else 1
-/
theorem finprod_eq_if {p : Prop} [Decidable p] {x : M} : ∏ᶠ _ : p, x = if p then x else 1 :=
  finprod_eq_dif fun _ => x

@[to_additive]
/-
**finprod_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_congr {f g : α -> M} (h : forall x, f x = g x) : finprod f = finpr
od g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem finprod_congr {f g : α → M} (h : ∀ x, f x = g x) : finprod f = finprod g :=
  congr_arg _ <| funext h

@[to_additive (attr := congr)]
/-
**finprod_congr_Prop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_congr_Prop {p q : Prop} {f : p -> M} {g : q -> M} (hpq : p = q) (h
fg : forall h : q, f (hpq.mpr h) = g h) : finprod f = finprod g
参数：hpq : p = q；hfg : forall h : q, f (hpq.mpr h) = g h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_congr`：finprod_congr {f g : α -> M} (h : forall x, f x = g x) : 
finprod f = finprod g
-/
theorem finprod_congr_Prop {p q : Prop} {f : p → M} {g : q → M} (hpq : p = q)
    (hfg : ∀ h : q, f (hpq.mpr h) = g h) : finprod f = finprod g := by
  subst q
  exact finprod_congr hfg

/-- To prove a property of a finite product, it suffices to prove that the property is
multiplicative and holds on the factors. -/
@[to_additive
      /-- To prove a property of a finite sum, it suffices to prove that the property is
      additive and holds on the summands. -/]
/-
**finprod_induction** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_induction {f : α -> M} (p : M -> Prop) (hp₀ : p 1) (hp₁ : forall x
 y, p x -> p y -> p (x * y)) (hp₂ : forall i, p (f i)) : p (∏ᶠ i, f i)
参数：p : M -> Prop；hp₀ : p 1；hp₁ : forall x y, p x -> p y -> p (x * y)；hp₂ : foral
l i, p (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_def'`：∀ {M : Type u_7} {α : Sort u_8} [inst : CommMonoid M] (f :
 α → M),   finprod f = if h : Function.HasFiniteMulSupport (f ∘ PLift.down) then
 ∏…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Finset.prod_induction`：prod_induction {M : Type*} [CommMonoid M] (f : ι 
-> M) (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (
base : fora…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem finprod_induction {f : α → M} (p : M → Prop) (hp₀ : p 1)
    (hp₁ : ∀ x y, p x → p y → p (x * y)) (hp₂ : ∀ i, p (f i)) : p (∏ᶠ i, f i) := by
  rw [finprod]
  split_ifs
  exacts [Finset.prod_induction _ _ hp₁ hp₀ fun i _ => hp₂ _, hp₀]
/-
**finprod_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_nonneg {R : Type*} [CommMonoidWithZero R] [Preorder R] [ZeroLEOneC
lass R] [PosMulMono R] {f : α -> R} (hf : forall x, 0 <= f x) : 0 <= ∏ᶠ x, f x
参数：hf : forall x, 0 <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_induction`：finprod_induction {f : α -> M} (p : M -> Prop) (hp₀ :
 p 1) (hp₁ : forall x y, p x -> p y -> p (x * y)) (hp₂ : forall i, p (f i)) : p 
(∏ᶠ i, …
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
-/
theorem finprod_nonneg {R : Type*} [CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R]
    [PosMulMono R] {f : α → R} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ ∏ᶠ x, f x :=
  finprod_induction (fun x => 0 ≤ x) zero_le_one (fun _ _ => mul_nonneg) hf

@[to_additive finsum_nonneg]
/-
**one_le_finprod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_finprod' {M : Type*} [CommMonoid M] [Preorder M] [IsOrderedMonoid M
] {f : α -> M} (hf : forall i, 1 <= f i) : 1 <= ∏ᶠ i, f i
参数：hf : forall i, 1 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_induction`：finprod_induction {f : α -> M} (p : M -> Prop) (hp₀ :
 p 1) (hp₁ : forall x y, p x -> p y -> p (x * y)) (hp₂ : forall i, p (f i)) : p 
(∏ᶠ i, …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `one_le_mul`：∀ {α : Type u_1} [inst : MulOneClass α] [inst_1 : Preorder α
] [MulLeftMono α] {a b : α}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem one_le_finprod' {M : Type*} [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
    {f : α → M} (hf : ∀ i, 1 ≤ f i) :
    1 ≤ ∏ᶠ i, f i :=
  finprod_induction _ le_rfl (fun _ _ => one_le_mul) hf

/-- A version of `one_le_finprod'` for `PosMulMono` in place of `MulLeftMono`. -/
/-
**one_le_finprod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_le_finprod {M : Type*} [CommMonoidWithZero M] [Preorder M] [ZeroLEOneC
lass M] [PosMulMono M] {f : α -> M} (hf : forall i, 1 <= f i) : 1 <= ∏ᶠ i, f i
参数：hf : forall i, 1 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_induction`：finprod_induction {f : α -> M} (p : M -> Prop) (hp₀ :
 p 1) (hp₁ : forall x y, p x -> p y -> p (x * y)) (hp₂ : forall i, p (f i)) : p 
(∏ᶠ i, …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `one_le_mul_of_one_le_of_one_le`：one_le_mul_of_one_le_of_one_le [ZeroLEOn
eClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hb : 1 <= b) : (1 : M₀) <= a * b

--- 原说明 ---
A version of `one_le_finprod'` for `PosMulMono` in place of `MulLeftMono`.
-/
lemma one_le_finprod {M : Type*} [CommMonoidWithZero M] [Preorder M] [ZeroLEOneClass M]
    [PosMulMono M] {f : α → M} (hf : ∀ i, 1 ≤ f i) :
    1 ≤ ∏ᶠ i, f i :=
  finprod_induction _ le_rfl (fun _ _ ↦ one_le_mul_of_one_le_of_one_le) hf

@[to_additive]
/-
**MonoidHom.map_finprod_plift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.map_finprod_plift (f : M ->* N) (g : α -> M) (h : HasFiniteMulSu
pport <| g ∘ PLift.down) : f (∏ᶠ x, g x) = ∏ᶠ x, f (g x)
参数：f : M ->* N；g : α -> M；h : HasFiniteMulSupport <| g ∘ PLift.down。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_prod_plift_of_mulSupport_subset`：finprod_eq_prod_plift_of_mul
Support_subset {f : α -> M} {s : Finset (PLift α)} (hs : mulSupport (f ∘ PLift.d
own) subseteq s) : ∏ᶠ i, f i = ∏…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用引理 `Function.mulSupport_comp_subset`：mulSupport_comp_subset {g : M -> N} (hg
 : g 1 = 1) (f : ι -> M) : mulSupport (g ∘ f) subseteq mulSupport f
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem MonoidHom.map_finprod_plift (f : M →* N) (g : α → M)
    (h : HasFiniteMulSupport <| g ∘ PLift.down) : f (∏ᶠ x, g x) = ∏ᶠ x, f (g x) := by
  rw [finprod_eq_prod_plift_of_mulSupport_subset h.coe_toFinset.ge,
    finprod_eq_prod_plift_of_mulSupport_subset, _root_.map_prod]
  rw [h.coe_toFinset]
  exact mulSupport_comp_subset f.map_one (g ∘ PLift.down)

@[to_additive]
/-
**MonoidHom.map_finprod_Prop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.map_finprod_Prop {p : Prop} (f : M ->* N) (g : p -> M) : f (∏ᶠ x
, g x) = ∏ᶠ x, f (g x)
参数：f : M ->* N；g : p -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_finprod_plift`：MonoidHom.map_finprod_plift (f : M ->* N) (
g : α -> M) (h : HasFiniteMulSupport <| g ∘ PLift.down) : f (∏ᶠ x, g x) = ∏ᶠ x, 
f (g x)
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `instFinitePLift`：∀ {α : Sort u_1} [Finite α], Finite (PLift α)
-/
theorem MonoidHom.map_finprod_Prop {p : Prop} (f : M →* N) (g : p → M) :
    f (∏ᶠ x, g x) = ∏ᶠ x, f (g x) :=
  f.map_finprod_plift g (Set.toFinite _)

@[to_additive]
/-
**MonoidHom.map_finprod_of_preimage_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.map_finprod_of_preimage_one (f : M ->* N) (hf : forall x, f x = 
1 -> x = 1) (g : α -> M) : f (∏ᶠ i, g i) = ∏ᶠ i, f (g i)
参数：f : M ->* N；hf : forall x, f x = 1 -> x = 1；g : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_finprod_plift`：MonoidHom.map_finprod_plift (f : M ->* N) (
g : α -> M) (h : HasFiniteMulSupport <| g ∘ PLift.down) : f (∏ᶠ x, g x) = ∏ᶠ x, 
f (g x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_def'`：∀ {M : Type u_7} {α : Sort u_8} [inst : CommMonoid M] (f :
 α → M),   finprod f = if h : Function.HasFiniteMulSupport (f ∘ PLift.down) then
 ∏…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem MonoidHom.map_finprod_of_preimage_one (f : M →* N) (hf : ∀ x, f x = 1 → x = 1) (g : α → M) :
    f (∏ᶠ i, g i) = ∏ᶠ i, f (g i) := by
  by_cases hg : HasFiniteMulSupport <| g ∘ PLift.down; · exact f.map_finprod_plift g hg
  rw [finprod, dif_neg, f.map_one, finprod, dif_neg]
  exacts [Infinite.mono (fun x hx => mt (hf (g x.down)) hx) hg, hg]

@[to_additive]
/-
**MonoidHom.map_finprod_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.map_finprod_of_injective (g : M ->* N) (hg : Injective g) (f : α
 -> M) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i)
参数：g : M ->* N；hg : Injective g；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_finprod_of_preimage_one`：MonoidHom.map_finprod_of_preimage
_one (f : M ->* N) (hf : forall x, f x = 1 -> x = 1) (g : α -> M) : f (∏ᶠ i, g i
) = ∏ᶠ i, f (g i)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
-/
theorem MonoidHom.map_finprod_of_injective (g : M →* N) (hg : Injective g) (f : α → M) :
    g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  g.map_finprod_of_preimage_one (fun _ => (hg.eq_iff' g.map_one).mp) f

@[to_additive]
/-
**MulEquiv.map_finprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulEquiv.map_finprod (g : M ≃* N) (f : α -> M) : g (∏ᶠ i, f i) = ∏ᶠ i, g (
f i)
参数：g : M ≃* N；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_finprod_of_injective`：MonoidHom.map_finprod_of_injective (
g : M ->* N) (hg : Injective g) (f : α -> M) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i)
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
-/
theorem MulEquiv.map_finprod (g : M ≃* N) (f : α → M) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  g.toMonoidHom.map_finprod_of_injective (EquivLike.injective g) f

@[to_additive]
/-
**MulEquivClass.map_finprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulEquivClass.map_finprod {F : Type*} [EquivLike F M N] [MulEquivClass F M
 N] (g : F) (f : α -> M) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i)
参数：g : F；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.map_finprod`：MulEquiv.map_finprod (g : M ≃* N) (f : α -> M) : g
 (∏ᶠ i, f i) = ∏ᶠ i, g (f i)
-/
theorem MulEquivClass.map_finprod {F : Type*} [EquivLike F M N] [MulEquivClass F M N] (g : F)
    (f : α → M) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  MulEquiv.map_finprod (MulEquivClass.toMulEquiv g) f

/-- The torsion-free assumption makes sure that the result holds even when the support of `f` is
infinite. For a more usual version assuming `HasFiniteSupport f` instead, see `finsum_smul'`. -/
/-
**finsum_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsum_smul {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M] [Module R
 M] [Module.IsTorsionFree R M] (f : ι -> R) (x : M) : (∑ᶠ i, f i) • x = ∑ᶠ i, f 
i • x
参数：f : ι -> R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finsum_zero`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid M], ∑
ᶠ (x : α), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidHom.map_finsum_of_injective`：∀ {M : Type u_2} {N : Type u_3} {α
 : Sort u_4} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] (g : M →+ N),  
 Function.Injective ⇑g → ∀…
· 使用引理 `smul_left_injective`：smul_left_injective (hm : m != 0) : ((· • m) : R ->
 M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α

--- 原说明 ---
The torsion-free assumption makes sure that the result holds even when the suppo
rt of `f` is
infinite. For a more usual version assuming `HasFiniteSupport f` instead, see `f
insum_smul'`.
-/
theorem finsum_smul {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] (f : ι → R) (x : M) : (∑ᶠ i, f i) • x = ∑ᶠ i, f i • x := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  · exact ((smulAddHom R M).flip x).map_finsum_of_injective (smul_left_injective R hx) _

/-- The torsion-free assumption makes sure that the result holds even when the support of `f` is
infinite. For a more usual version assuming `HasFiniteSupport f` instead, see `smul_finsum'`. -/
/-
**smul_finsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_finsum {R M : Type*} [Semiring R] [IsDomain R] [AddCommGroup M] [Modu
le R M] [Module.IsTorsionFree R M] (c : R) (f : ι -> M) : c • ∑ᶠ i, f i = ∑ᶠ i, 
c • f i
参数：c : R；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finsum_zero`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid M], ∑
ᶠ (x : α), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidHom.map_finsum_of_injective`：∀ {M : Type u_2} {N : Type u_3} {α
 : Sort u_4} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] (g : M →+ N),  
 Function.Injective ⇑g → ∀…
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α

--- 原说明 ---
The torsion-free assumption makes sure that the result holds even when the suppo
rt of `f` is
infinite. For a more usual version assuming `HasFiniteSupport f` instead, see `s
mul_finsum'`.
-/
theorem smul_finsum {R M : Type*} [Semiring R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] (c : R) (f : ι → M) : c • ∑ᶠ i, f i = ∑ᶠ i, c • f i := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp
  · exact (smulAddHom R M c).map_finsum_of_injective (smul_right_injective M hc) _

@[to_additive]
/-
**finprod_inv_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_inv_distrib [DivisionCommMonoid G] (f : α -> G) : (∏ᶠ x, (f x)⁻¹) 
= (∏ᶠ x, f x)⁻¹
参数：f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulEquiv.map_finprod`：MulEquiv.map_finprod (g : M ≃* N) (f : α -> M) : g
 (∏ᶠ i, f i) = ∏ᶠ i, g (f i)
-/
theorem finprod_inv_distrib [DivisionCommMonoid G] (f : α → G) : (∏ᶠ x, (f x)⁻¹) = (∏ᶠ x, f x)⁻¹ :=
  ((MulEquiv.inv G).map_finprod f).symm

end sort

section type

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

@[to_additive]
/-
**finprod_eq_mulIndicator_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_eq_mulIndicator_apply (s : Set α) (f : α -> M) (a : α) : ∏ᶠ _ : a 
in s, f a = mulIndicator s f a
参数：s : Set α；f : α -> M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_eq_if`：finprod_eq_if {p : Prop} [Decidable p] {x : M} : ∏ᶠ _ : p
, x = if p then x else 1
-/
theorem finprod_eq_mulIndicator_apply (s : Set α) (f : α → M) (a : α) :
    ∏ᶠ _ : a ∈ s, f a = mulIndicator s f a := by
  convert! finprod_eq_if (M := M) (p := a ∈ s) (x := f a)

@[to_additive (attr := simp)]
/-
**finprod_apply_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_apply_ne_one (f : α -> M) (a : α) : ∏ᶠ _ : f a != 1, f a = f a
参数：f : α -> M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Function.mem_mulSupport`：mem_mulSupport : x in mulSupport f ↔ f x != 1
· 使用定理 `finprod_eq_mulIndicator_apply`：finprod_eq_mulIndicator_apply (s : Set α)
 (f : α -> M) (a : α) : ∏ᶠ _ : a in s, f a = mulIndicator s f a
· 使用引理 `Set.mulIndicator_mulSupport`：mulIndicator_mulSupport : mulIndicator (mul
Support f) f = f
-/
theorem finprod_apply_ne_one (f : α → M) (a : α) : ∏ᶠ _ : f a ≠ 1, f a = f a := by
  rw [← mem_mulSupport, finprod_eq_mulIndicator_apply, mulIndicator_mulSupport]

@[to_additive]
/-
**finprod_mem_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_def (s : Set α) (f : α -> M) : ∏ᶠ a in s, f a = ∏ᶠ a, mulIndic
ator s f a
参数：s : Set α；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_congr`：finprod_congr {f g : α -> M} (h : forall x, f x = g x) : 
finprod f = finprod g
· 使用定理 `finprod_eq_mulIndicator_apply`：finprod_eq_mulIndicator_apply (s : Set α)
 (f : α -> M) (a : α) : ∏ᶠ _ : a in s, f a = mulIndicator s f a
-/
theorem finprod_mem_def (s : Set α) (f : α → M) : ∏ᶠ a ∈ s, f a = ∏ᶠ a, mulIndicator s f a :=
  finprod_congr <| finprod_eq_mulIndicator_apply s f

@[to_additive]
/-
**finprod_mem_mulSupport** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finprod_mem_mulSupport (f : α -> M) : ∏ᶠ a in mulSupport f, f a = ∏ᶠ a, f 
a
参数：f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_mem_def`：finprod_mem_def (s : Set α) (f : α -> M) : ∏ᶠ a in s, f
 a = ∏ᶠ a, mulIndicator s f a
· 使用引理 `Set.mulIndicator_mulSupport`：mulIndicator_mulSupport : mulIndicator (mul
Support f) f = f
-/
lemma finprod_mem_mulSupport (f : α → M) : ∏ᶠ a ∈ mulSupport f, f a = ∏ᶠ a, f a := by
  rw [finprod_mem_def, mulIndicator_mulSupport]

@[to_additive]
/-
**finprod_eq_prod_of_mulSupport_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_eq_prod_of_mulSupport_subset (f : α -> M) {s : Finset α} (h : mulS
upport f subseteq s) : ∏ᶠ i, f i = ∏ i in s, f i
参数：f : α -> M；h : mulSupport f subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.mulSupport_comp_eq_preimage`：mulSupport_comp_eq_preimage (g : κ
 -> M) (f : ι -> κ) : mulSupport (g ∘ f) = f ⁻¹' mulSupport g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `finprod_eq_prod_plift_of_mulSupport_subset`：finprod_eq_prod_plift_of_mul
Support_subset {f : α -> M} {s : Finset (PLift α)} (hs : mulSupport (f ∘ PLift.d
own) subseteq s) : ∏ᶠ i, f i = ∏…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
-/
theorem finprod_eq_prod_of_mulSupport_subset (f : α → M) {s : Finset α} (h : mulSupport f ⊆ s) :
    ∏ᶠ i, f i = ∏ i ∈ s, f i := by
  have A : mulSupport (f ∘ PLift.down) = Equiv.plift.symm '' mulSupport f := by
    rw [mulSupport_comp_eq_preimage]
    exact (Equiv.plift.symm.image_eq_preimage_symm _).symm
  have : mulSupport (f ∘ PLift.down) ⊆ s.map Equiv.plift.symm.toEmbedding := by
    rw [A, Finset.coe_map]
    exact image_mono h
  rw [finprod_eq_prod_plift_of_mulSupport_subset this]
  simp only [Finset.prod_map, Equiv.coe_toEmbedding]
  congr

@[to_additive]
/-
**finprod_eq_prod_of_mulSupport_toFinset_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_eq_prod_of_mulSupport_toFinset_subset (f : α -> M) (hf : HasFinite
MulSupport f) {s : Finset α} (h : hf.toFinset subseteq s) : ∏ᶠ i, f i = ∏ i in s
, f i
参数：f : α -> M；hf : HasFiniteMulSupport f；h : hf.toFinset subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
-/
theorem finprod_eq_prod_of_mulSupport_toFinset_subset (f : α → M) (hf : HasFiniteMulSupport f)
    {s : Finset α} (h : hf.toFinset ⊆ s) : ∏ᶠ i, f i = ∏ i ∈ s, f i :=
  finprod_eq_prod_of_mulSupport_subset _ fun _ hx => h <| hf.mem_toFinset.2 hx

@[to_additive]
/-
**finprod_eq_prod_of_mulSupport_subset_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_eq_prod_of_mulSupport_subset_of_finite (f : α -> M) {s : Set α} (h
 : mulSupport f subseteq s) (hs : s.Finite) : ∏ᶠ i, f i = ∏ i in hs.toFinset, f 
i
参数：f : α -> M；h : mulSupport f subseteq s；hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
-/
theorem finprod_eq_prod_of_mulSupport_subset_of_finite (f : α → M) {s : Set α}
    (h : mulSupport f ⊆ s) (hs : s.Finite) : ∏ᶠ i, f i = ∏ i ∈ hs.toFinset, f i :=
  finprod_eq_prod_of_mulSupport_subset f <| by rwa [Set.Finite.coe_toFinset]

@[to_additive]
/-
**finprod_eq_finsetProd_of_mulSupport_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_eq_finsetProd_of_mulSupport_subset (f : α -> M) {s : Finset α} (h 
: mulSupport f subseteq (s : Set α)) : ∏ᶠ i, f i = ∏ i in s, f i
参数：f : α -> M；h : mulSupport f subseteq (s : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_eq_prod_of_mulSupport_toFinset_subset`：finprod_eq_prod_of_mulSup
port_toFinset_subset (f : α -> M) (hf : HasFiniteMulSupport f) {s : Finset α} (h
 : hf.toFinset subseteq s) : ∏ᶠ i, …
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem finprod_eq_finsetProd_of_mulSupport_subset (f : α → M) {s : Finset α}
    (h : mulSupport f ⊆ (s : Set α)) : ∏ᶠ i, f i = ∏ i ∈ s, f i :=
  haveI h' : (s.finite_toSet.subset h).toFinset ⊆ s := by
    simpa [← Finset.coe_subset, Set.coe_toFinset]
  finprod_eq_prod_of_mulSupport_toFinset_subset _ _ h'

@[deprecated (since := "2026-04-08")]
alias finsum_eq_finset_sum_of_support_subset := finsum_eq_finsetSum_of_support_subset

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finprod_eq_finset_prod_of_mulSupport_subset := finprod_eq_finsetProd_of_mulSupport_subset

@[to_additive]
/-
**finprod_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_def (f : α -> M) [Decidable (HasFiniteMulSupport f)] : ∏ᶠ i : α, f
 i = if h : HasFiniteMulSupport f then ∏ i in h.toFinset, f i else 1
参数：f : α -> M；HasFiniteMulSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `finprod_eq_prod_of_mulSupport_toFinset_subset`：finprod_eq_prod_of_mulSup
port_toFinset_subset (f : α -> M) (hf : HasFiniteMulSupport f) {s : Finset α} (h
 : hf.toFinset subseteq s) : ∏ᶠ i, …
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `finprod_def'`：∀ {M : Type u_7} {α : Sort u_8} [inst : CommMonoid M] (f :
 α → M),   finprod f = if h : Function.HasFiniteMulSupport (f ∘ PLift.down) then
 ∏…
· 使用定理 `Function.HasFiniteMulSupport.eq_1`：∀ {α : Type u_1} {M : Type u_2} [inst
 : One M] (f : α → M),   Function.HasFiniteMulSupport f = (Function.mulSupport f
).Finite
· 使用引理 `Function.mulSupport_comp_eq_preimage`：mulSupport_comp_eq_preimage (g : κ
 -> M) (f : ι -> κ) : mulSupport (g ∘ f) = f ⁻¹' mulSupport g
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Set.Finite.of_preimage`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set
 β}, (f ⁻¹' s).Finite → Function.Surjective f → s.Finite
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem finprod_def (f : α → M) [Decidable (HasFiniteMulSupport f)] :
    ∏ᶠ i : α, f i = if h : HasFiniteMulSupport f then ∏ i ∈ h.toFinset, f i else 1 := by
  split_ifs with h
  · exact finprod_eq_prod_of_mulSupport_toFinset_subset _ h (Finset.Subset.refl _)
  · rw [finprod, dif_neg]
    rw [HasFiniteMulSupport, mulSupport_comp_eq_preimage]
    exact mt (fun hf => hf.of_preimage Equiv.plift.surjective) h

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**finprod_of_infinite_mulSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_of_infinite_mulSupport {f : α -> M} (hf : (mulSupport f).Infinite)
 : ∏ᶠ i, f i = 1
参数：hf : (mulSupport f).Infinite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_def`：finprod_def (f : α -> M) [Decidable (HasFiniteMulSupport f)
] : ∏ᶠ i : α, f i = if h : HasFiniteMulSupport f then ∏ i in h.toFinset, f i els
e…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem finprod_of_infinite_mulSupport {f : α → M} (hf : (mulSupport f).Infinite) :
    ∏ᶠ i, f i = 1 := by
  classical
  rw [finprod_def]
  simp only [HasFiniteMulSupport]
  rw [dif_neg hf]

@[to_additive]
/-
**finprod_of_not_hasFiniteMulSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_of_not_hasFiniteMulSupport {f : α -> M} (hf : ¬ f.HasFiniteMulSupp
ort) : ∏ᶠ i, f i = 1
参数：hf : ¬ f.HasFiniteMulSupport。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_of_infinite_mulSupport`：finprod_of_infinite_mulSupport {f : α ->
 M} (hf : (mulSupport f).Infinite) : ∏ᶠ i, f i = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_finite`：not_finite {s : Set α} : ¬s.Finite ↔ s.Infinite
-/
theorem finprod_of_not_hasFiniteMulSupport {f : α → M} (hf : ¬ f.HasFiniteMulSupport) :
    ∏ᶠ i, f i = 1 :=
  finprod_of_infinite_mulSupport <| Set.not_finite.mp hf

@[to_additive]
/-
**hasFiniteMulSupport_of_finprod_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFiniteMulSupport_of_finprod_ne_one {f : α -> M} (h : ∏ᶠ i, f i != 1) : 
HasFiniteMulSupport f
参数：h : ∏ᶠ i, f i != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_infinite`：not_infinite {s : Set α} : ¬s.Infinite ↔ s.Finite
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `finprod_of_infinite_mulSupport`：finprod_of_infinite_mulSupport {f : α ->
 M} (hf : (mulSupport f).Infinite) : ∏ᶠ i, f i = 1
-/
theorem hasFiniteMulSupport_of_finprod_ne_one {f : α → M} (h : ∏ᶠ i, f i ≠ 1) :
    HasFiniteMulSupport f :=
  not_infinite.mp <| (finprod_of_infinite_mulSupport ·).mt h

@[deprecated (since := "2026-03-03")] alias
  finite_mulSupport_of_finprod_ne_one := hasFiniteMulSupport_of_finprod_ne_one

@[deprecated (since := "2026-03-03")] alias
  finite_support_of_finsum_ne_zero := hasFiniteSupport_of_finsum_ne_zero
/-
**hasFiniteSupport_of_finsum_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFiniteSupport_of_finsum_eq_one {R : Type*} [NonAssocSemiring R] {f : α 
-> R} (h : ∑ᶠ i, f i = 1) : HasFiniteSupport f
参数：h : ∑ᶠ i, f i = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.support_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M]
 [Subsingleton M] (f : ι → M), Function.support f = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `hasFiniteSupport_of_finsum_ne_zero`：∀ {α : Type u_1} {M : Type u_5} [ins
t : AddCommMonoid M] {f : α → M}, ∑ᶠ (i : α), f i ≠ 0 → Function.HasFiniteSuppor
t f
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem hasFiniteSupport_of_finsum_eq_one {R : Type*} [NonAssocSemiring R] {f : α → R}
    (h : ∑ᶠ i, f i = 1) : HasFiniteSupport f := by
  cases subsingleton_or_nontrivial R
  · simp_rw [HasFiniteSupport, Subsingleton.support_eq, finite_empty]
  · apply hasFiniteSupport_of_finsum_ne_zero
    rw [h]
    exact one_ne_zero

@[deprecated (since := "2026-03-03")] alias
  finite_support_of_finsum_eq_one := hasFiniteSupport_of_finsum_eq_one

@[to_additive]
/-
**finprod_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_eq_prod (f : α -> M) (hf : HasFiniteMulSupport f) : ∏ᶠ i : α, f i 
= ∏ i in hf.toFinset, f i
参数：f : α -> M；hf : HasFiniteMulSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_def`：finprod_def (f : α -> M) [Decidable (HasFiniteMulSupport f)
] : ∏ᶠ i : α, f i = if h : HasFiniteMulSupport f then ∏ i in h.toFinset, f i els
e…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem finprod_eq_prod (f : α → M) (hf : HasFiniteMulSupport f) :
    ∏ᶠ i : α, f i = ∏ i ∈ hf.toFinset, f i := by classical rw [finprod_def, dif_pos hf]

@[to_additive]
/-
**finprod_eq_prod_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_eq_prod_of_fintype [Fintype α] (f : α -> M) : ∏ᶠ i : α, f i = ∏ i,
 f i
参数：f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_eq_prod_of_mulSupport_toFinset_subset`：finprod_eq_prod_of_mulSup
port_toFinset_subset (f : α -> M) (hf : HasFiniteMulSupport f) {s : Finset α} (h
 : hf.toFinset subseteq s) : ∏ᶠ i, …
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
-/
theorem finprod_eq_prod_of_fintype [Fintype α] (f : α → M) : ∏ᶠ i : α, f i = ∏ i, f i :=
  finprod_eq_prod_of_mulSupport_toFinset_subset _ (Set.toFinite _) <| Finset.subset_univ _
/-
**finprod_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_ne_zero {M₀ : Type*} [CommMonoidWithZero M₀] [Nontrivial M₀] [NoZe
roDivisors M₀] {f : α -> M₀} (h : forall i, f i != 0) : ∏ᶠ i, f i != 0
参数：h : forall i, f i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_of_infinite_mulSupport`：finprod_of_infinite_mulSupport {f : α ->
 M} (hf : (mulSupport f).Infinite) : ∏ᶠ i, f i = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem finprod_ne_zero {M₀ : Type*} [CommMonoidWithZero M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
    {f : α → M₀} (h : ∀ i, f i ≠ 0) :
    ∏ᶠ i, f i ≠ 0 := by
  by_cases h₂ : Set.Finite f.mulSupport
  · grind [finprod_eq_prod f h₂, Finset.prod_ne_zero_iff]
  · simp [finprod_of_infinite_mulSupport h₂]
/-
**finprod_apply_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_apply_ne_zero {ι : Type*} {N₀ M₀ : Type*} [CommMonoidWithZero M₀] 
[Nontrivial M₀] [NoZeroDivisors M₀] {n : N₀} {f : ι -> N₀ -> M₀} (h : forall i, 
f i n != 0) : (∏ᶠ i, f i) n != 0
参数：h : forall i, f i n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_prod`：finprod_eq_prod (f : α -> M) (hf : HasFiniteMulSupport 
f) : ∏ᶠ i : α, f i = ∏ i in hf.toFinset, f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `finprod_of_infinite_mulSupport`：finprod_of_infinite_mulSupport {f : α ->
 M} (hf : (mulSupport f).Infinite) : ∏ᶠ i, f i = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem finprod_apply_ne_zero {ι : Type*} {N₀ M₀ : Type*} [CommMonoidWithZero M₀] [Nontrivial M₀]
    [NoZeroDivisors M₀] {n : N₀} {f : ι → N₀ → M₀} (h : ∀ i, f i n ≠ 0) :
    (∏ᶠ i, f i) n ≠ 0 := by
  by_cases h₂ : f.mulSupport.Finite
  · rw [finprod_eq_prod f h₂]
    grind [Finset.prod_apply, Finset.prod_ne_zero_iff]
  · simp [finprod_of_infinite_mulSupport h₂]

@[to_additive]
/-
**map_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_finsetProd {α F : Type*} [Fintype α] [EquivLike F M N] [MulEquivClass 
F M N] (f : F) (g : α -> M) : f (∏ i : α, g i) = ∏ i : α, f (g i)
参数：f : F；g : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquivClass.map_finprod`：MulEquivClass.map_finprod {F : Type*} [EquivL
ike F M N] [MulEquivClass F M N] (g : F) (f : α -> M) : g (∏ᶠ i, f i) = ∏ᶠ i, g 
(f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_finsetProd {α F : Type*} [Fintype α] [EquivLike F M N] [MulEquivClass F M N] (f : F)
    (g : α → M) : f (∏ i : α, g i) = ∏ i : α, f (g i) := by
  simp [← finprod_eq_prod_of_fintype, MulEquivClass.map_finprod]

@[deprecated (since := "2026-04-08")] alias map_finset_sum := map_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias map_finset_prod := map_finsetProd

@[to_additive]
/-
**finprod_cond_eq_prod_of_cond_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_cond_eq_prod_of_cond_iff (f : α -> M) {p : α -> Prop} {t : Finset 
α} (h : forall {x}, f x != 1 -> (p x ↔ x in t)) : (∏ᶠ (i) (_ : p i), f i) = ∏ i 
in t, f i
参数：f : α -> M；h : forall {x}, f x != 1 -> (p x ↔ x in t)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulSupport_mulIndicator`：mulSupport_mulIndicator : Function.mulSuppo
rt (s.mulIndicator f) = s inter Function.mulSupport f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `finprod_mem_def`：finprod_mem_def (s : Set α) (f : α -> M) : ∏ᶠ a in s, f
 a = ∏ᶠ a, mulIndicator s f a
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.mulIndicator_apply_eq_self`：mulIndicator_apply_eq_self : s.mulIndica
tor f a = f a ↔ a ∉ s -> f a = 1
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
-/
theorem finprod_cond_eq_prod_of_cond_iff (f : α → M) {p : α → Prop} {t : Finset α}
    (h : ∀ {x}, f x ≠ 1 → (p x ↔ x ∈ t)) : (∏ᶠ (i) (_ : p i), f i) = ∏ i ∈ t, f i := by
  set s := { x | p x }
  change ∏ᶠ (i : α) (_ : i ∈ s), f i = ∏ i ∈ t, f i
  have : mulSupport (s.mulIndicator f) ⊆ t := by
    rw [Set.mulSupport_mulIndicator]
    intro x hx
    exact (h hx.2).1 hx.1
  rw [finprod_mem_def, finprod_eq_prod_of_mulSupport_subset _ this]
  refine Finset.prod_congr rfl fun x hx => mulIndicator_apply_eq_self.2 fun hxs => ?_
  contrapose! hxs
  exact (h hxs).2 hx

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**finprod_cond_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_cond_ne (f : α -> M) (a : α) [DecidableEq α] (hf : HasFiniteMulSup
port f) : (∏ᶠ (i) (_ : i != a), f i) = ∏ i in hf.toFinset.erase a, f i
参数：f : α -> M；a : α；hf : HasFiniteMulSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_cond_eq_prod_of_cond_iff`：finprod_cond_eq_prod_of_cond_iff (f : 
α -> M) {p : α -> Prop} {t : Finset α} (h : forall {x}, f x != 1 -> (p x ↔ x in 
t)) : (∏ᶠ (i) (_ : p i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用引理 `Function.mem_mulSupport`：mem_mulSupport : x in mulSupport f ↔ f x != 1
-/
theorem finprod_cond_ne (f : α → M) (a : α) [DecidableEq α] (hf : HasFiniteMulSupport f) :
    (∏ᶠ (i) (_ : i ≠ a), f i) = ∏ i ∈ hf.toFinset.erase a, f i := by
  apply finprod_cond_eq_prod_of_cond_iff
  intro x hx
  rw [Finset.mem_erase, Finite.mem_toFinset, mem_mulSupport]
  grind

@[to_additive]
/-
**finprod_mem_eq_prod_of_inter_mulSupport_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_eq_prod_of_inter_mulSupport_eq (f : α -> M) {s : Set α} {t : F
inset α} (h : s inter mulSupport f = ↑t inter mulSupport f) : ∏ᶠ i in s, f i = ∏
 i in t, f i
参数：f : α -> M；h : s inter mulSupport f = ↑t inter mulSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_cond_eq_prod_of_cond_iff`：finprod_cond_eq_prod_of_cond_iff (f : 
α -> M) {p : α -> Prop} {t : Finset α} (h : forall {x}, f x != 1 -> (p x ↔ x in 
t)) : (∏ᶠ (i) (_ : p i…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用引理 `Function.mem_mulSupport`：mem_mulSupport : x in mulSupport f ↔ f x != 1
-/
theorem finprod_mem_eq_prod_of_inter_mulSupport_eq (f : α → M) {s : Set α} {t : Finset α}
    (h : s ∩ mulSupport f = ↑t ∩ mulSupport f) : ∏ᶠ i ∈ s, f i = ∏ i ∈ t, f i :=
  finprod_cond_eq_prod_of_cond_iff _ <| by
    intro x hxf
    rw [← mem_mulSupport] at hxf
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · refine ((mem_inter_iff x t (mulSupport f)).mp ?_).1
      rw [← Set.ext_iff.mp h x, mem_inter_iff]
      exact ⟨hx, hxf⟩
    · refine ((mem_inter_iff x s (mulSupport f)).mp ?_).1
      rw [Set.ext_iff.mp h x, mem_inter_iff]
      exact ⟨hx, hxf⟩

@[to_additive]
/-
**finprod_mem_eq_prod_of_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_eq_prod_of_subset (f : α -> M) {s : Set α} {t : Finset α} (h₁ 
: s inter mulSupport f subseteq t) (h₂ : ↑t subseteq s) : ∏ᶠ i in s, f i = ∏ i i
n t, f i
参数：f : α -> M；h₁ : s inter mulSupport f subseteq t；h₂ : ↑t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_cond_eq_prod_of_cond_iff`：finprod_cond_eq_prod_of_cond_iff (f : 
α -> M) {p : α -> Prop} {t : Finset α} (h : forall {x}, f x != 1 -> (p x ↔ x in 
t)) : (∏ᶠ (i) (_ : p i…
-/
theorem finprod_mem_eq_prod_of_subset (f : α → M) {s : Set α} {t : Finset α}
    (h₁ : s ∩ mulSupport f ⊆ t) (h₂ : ↑t ⊆ s) : ∏ᶠ i ∈ s, f i = ∏ i ∈ t, f i :=
  finprod_cond_eq_prod_of_cond_iff _ fun hx => ⟨fun h => h₁ ⟨h, hx⟩, fun h => h₂ h⟩

@[to_additive]
/-
**finprod_mem_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_eq_prod (f : α -> M) {s : Set α} (hf : (s inter mulSupport f).
Finite) : ∏ᶠ i in s, f i = ∏ i in hf.toFinset, f i
参数：f : α -> M；hf : (s inter mulSupport f).Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_eq_prod_of_inter_mulSupport_eq`：finprod_mem_eq_prod_of_inter
_mulSupport_eq (f : α -> M) {s : Set α} {t : Finset α} (h : s inter mulSupport f
 = ↑t inter mulSupport f) : ∏ᶠ i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finprod_mem_eq_prod (f : α → M) {s : Set α} (hf : (s ∩ mulSupport f).Finite) :
    ∏ᶠ i ∈ s, f i = ∏ i ∈ hf.toFinset, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ <| by simp [inter_assoc]

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**finprod_mem_eq_prod_filter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_eq_prod_filter (f : α -> M) (s : Set α) [DecidablePred (· in s
)] (hf : HasFiniteMulSupport f) : ∏ᶠ i in s, f i = ∏ i in hf.toFinset with i in 
s, f i
参数：f : α -> M；s : Set α；· in s；hf : HasFiniteMulSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_eq_prod_of_inter_mulSupport_eq`：finprod_mem_eq_prod_of_inter
_mulSupport_eq (f : α -> M) {s : Set α} {t : Finset α} (h : s inter mulSupport f
 = ↑t inter mulSupport f) : ∏ᶠ i…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem finprod_mem_eq_prod_filter (f : α → M) (s : Set α) [DecidablePred (· ∈ s)]
    (hf : HasFiniteMulSupport f) :
    ∏ᶠ i ∈ s, f i = ∏ i ∈ hf.toFinset with i ∈ s, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ <| by
    ext x
    simp [and_comm]

@[to_additive]
/-
**finprod_mem_eq_toFinset_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_eq_toFinset_prod (f : α -> M) (s : Set α) [Fintype s] : ∏ᶠ i i
n s, f i = ∏ i in s.toFinset, f i
参数：f : α -> M；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_eq_prod_of_inter_mulSupport_eq`：finprod_mem_eq_prod_of_inter
_mulSupport_eq (f : α -> M) {s : Set α} {t : Finset α} (h : s inter mulSupport f
 = ↑t inter mulSupport f) : ∏ᶠ i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finprod_mem_eq_toFinset_prod (f : α → M) (s : Set α) [Fintype s] :
    ∏ᶠ i ∈ s, f i = ∏ i ∈ s.toFinset, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ <| by simp_rw [coe_toFinset s]

@[to_additive]
/-
**finprod_mem_eq_finite_toFinset_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_eq_finite_toFinset_prod (f : α -> M) {s : Set α} (hs : s.Finit
e) : ∏ᶠ i in s, f i = ∏ i in hs.toFinset, f i
参数：f : α -> M；hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_eq_prod_of_inter_mulSupport_eq`：finprod_mem_eq_prod_of_inter
_mulSupport_eq (f : α -> M) {s : Set α} {t : Finset α} (h : s inter mulSupport f
 = ↑t inter mulSupport f) : ∏ᶠ i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
-/
theorem finprod_mem_eq_finite_toFinset_prod (f : α → M) {s : Set α} (hs : s.Finite) :
    ∏ᶠ i ∈ s, f i = ∏ i ∈ hs.toFinset, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ <| by rw [hs.coe_toFinset]

@[to_additive]
/-
**finprod_mem_finset_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_finset_eq_prod (f : α -> M) (s : Finset α) : ∏ᶠ i in s, f i = 
∏ i in s, f i
参数：f : α -> M；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_eq_prod_of_inter_mulSupport_eq`：finprod_mem_eq_prod_of_inter
_mulSupport_eq (f : α -> M) {s : Set α} {t : Finset α} (h : s inter mulSupport f
 = ↑t inter mulSupport f) : ∏ᶠ i…
-/
theorem finprod_mem_finset_eq_prod (f : α → M) (s : Finset α) : ∏ᶠ i ∈ s, f i = ∏ i ∈ s, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ rfl

@[to_additive]
/-
**finprod_mem_coe_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_coe_finset (f : α -> M) (s : Finset α) : (∏ᶠ i in (s : Set α),
 f i) = ∏ i in s, f i
参数：f : α -> M；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_eq_prod_of_inter_mulSupport_eq`：finprod_mem_eq_prod_of_inter
_mulSupport_eq (f : α -> M) {s : Set α} {t : Finset α} (h : s inter mulSupport f
 = ↑t inter mulSupport f) : ∏ᶠ i…
-/
theorem finprod_mem_coe_finset (f : α → M) (s : Finset α) :
    (∏ᶠ i ∈ (s : Set α), f i) = ∏ i ∈ s, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ rfl

@[to_additive]
/-
**finprod_mem_eq_one_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_eq_one_of_infinite {f : α -> M} {s : Set α} (hs : (s inter mul
Support f).Infinite) : ∏ᶠ i in s, f i = 1
参数：hs : (s inter mulSupport f).Infinite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_mem_def`：finprod_mem_def (s : Set α) (f : α -> M) : ∏ᶠ a in s, f
 a = ∏ᶠ a, mulIndicator s f a
· 使用定理 `finprod_of_infinite_mulSupport`：finprod_of_infinite_mulSupport {f : α ->
 M} (hf : (mulSupport f).Infinite) : ∏ᶠ i, f i = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.mulSupport_mulIndicator`：mulSupport_mulIndicator : Function.mulSuppo
rt (s.mulIndicator f) = s inter Function.mulSupport f
-/
theorem finprod_mem_eq_one_of_infinite {f : α → M} {s : Set α} (hs : (s ∩ mulSupport f).Infinite) :
    ∏ᶠ i ∈ s, f i = 1 := by
  rw [finprod_mem_def]
  apply finprod_of_infinite_mulSupport
  rwa [← mulSupport_mulIndicator] at hs

@[to_additive]
/-
**finprod_mem_eq_one_of_forall_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_eq_one_of_forall_eq_one {f : α -> M} {s : Set α} (h : forall x
 in s, f x = 1) : ∏ᶠ i in s, f i = 1
参数：h : forall x in s, f x = 1。
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
· 使用定理 `finprod_congr_Prop`：finprod_congr_Prop {p q : Prop} {f : p -> M} {g : q 
-> M} (hpq : p = q) (hfg : forall h : q, f (hpq.mpr h) = g h) : finprod f = finp
rod g
· 使用定理 `finprod_one`：finprod_one : (∏ᶠ _ : α, (1 : M)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finprod_mem_eq_one_of_forall_eq_one {f : α → M} {s : Set α} (h : ∀ x ∈ s, f x = 1) :
    ∏ᶠ i ∈ s, f i = 1 := by simp +contextual [h]

@[to_additive]
/-
**finprod_mem_inter_mulSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_inter_mulSupport (f : α -> M) (s : Set α) : ∏ᶠ i in s inter mu
lSupport f, f i = ∏ᶠ i in s, f i
参数：f : α -> M；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_mem_def`：finprod_mem_def (s : Set α) (f : α -> M) : ∏ᶠ a in s, f
 a = ∏ᶠ a, mulIndicator s f a
· 使用引理 `Set.mulIndicator_inter_mulSupport`：mulIndicator_inter_mulSupport (s : Se
t α) (f : α -> M) : mulIndicator (s inter mulSupport f) f = mulIndicator s f
-/
theorem finprod_mem_inter_mulSupport (f : α → M) (s : Set α) :
    ∏ᶠ i ∈ s ∩ mulSupport f, f i = ∏ᶠ i ∈ s, f i := by
  rw [finprod_mem_def, finprod_mem_def, mulIndicator_inter_mulSupport]

@[to_additive]
/-
**finprod_mem_inter_mulSupport_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_inter_mulSupport_eq (f : α -> M) (s t : Set α) (h : s inter mu
lSupport f = t inter mulSupport f) : ∏ᶠ i in s, f i = ∏ᶠ i in t, f i
参数：f : α -> M；s t : Set α；h : s inter mulSupport f = t inter mulSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_mem_inter_mulSupport`：finprod_mem_inter_mulSupport (f : α -> M) 
(s : Set α) : ∏ᶠ i in s inter mulSupport f, f i = ∏ᶠ i in s, f i
-/
theorem finprod_mem_inter_mulSupport_eq (f : α → M) (s t : Set α)
    (h : s ∩ mulSupport f = t ∩ mulSupport f) : ∏ᶠ i ∈ s, f i = ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mulSupport, h, finprod_mem_inter_mulSupport]

@[to_additive]
/-
**finprod_mem_inter_mulSupport_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_inter_mulSupport_eq' (f : α -> M) (s t : Set α) (h : forall x 
in mulSupport f, x in s ↔ x in t) : ∏ᶠ i in s, f i = ∏ᶠ i in t, f i
参数：f : α -> M；s t : Set α；h : forall x in mulSupport f, x in s ↔ x in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_inter_mulSupport_eq`：finprod_mem_inter_mulSupport_eq (f : α 
-> M) (s t : Set α) (h : s inter mulSupport f = t inter mulSupport f) : ∏ᶠ i in 
s, f i = ∏ᶠ i in t, f…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_congr_left`：∀ {c a b : Prop}, (c → (a ↔ b)) → (a ∧ c ↔ b ∧ c)
-/
theorem finprod_mem_inter_mulSupport_eq' (f : α → M) (s t : Set α)
    (h : ∀ x ∈ mulSupport f, x ∈ s ↔ x ∈ t) : ∏ᶠ i ∈ s, f i = ∏ᶠ i ∈ t, f i := by
  apply finprod_mem_inter_mulSupport_eq
  ext x
  exact and_congr_left (h x)

@[to_additive]
/-
**finprod_mem_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_univ (f : α -> M) : ∏ᶠ i in @Set.univ α, f i = ∏ᶠ i : α, f i
参数：f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_congr`：finprod_congr {f g : α -> M} (h : forall x, f x = g x) : 
finprod f = finprod g
· 使用定理 `finprod_true`：finprod_true (f : True -> M) : ∏ᶠ i, f i = f trivial
-/
theorem finprod_mem_univ (f : α → M) : ∏ᶠ i ∈ @Set.univ α, f i = ∏ᶠ i : α, f i :=
  finprod_congr fun _ => finprod_true _

variable {f g : α → M} {a b : α} {s t : Set α}

@[to_additive]
/-
**finprod_mem_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_congr (h₀ : s = t) (h₁ : forall x in t, f x = g x) : ∏ᶠ i in s
, f i = ∏ᶠ i in t, g i
参数：h₀ : s = t；h₁ : forall x in t, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_congr`：finprod_congr {f g : α -> M} (h : forall x, f x = g x) : 
finprod f = finprod g
· 使用定理 `finprod_congr_Prop`：finprod_congr_Prop {p q : Prop} {f : p -> M} {g : q 
-> M} (hpq : p = q) (hfg : forall h : q, f (hpq.mpr h) = g h) : finprod f = finp
rod g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem finprod_mem_congr (h₀ : s = t) (h₁ : ∀ x ∈ t, f x = g x) :
    ∏ᶠ i ∈ s, f i = ∏ᶠ i ∈ t, g i :=
  h₀.symm ▸ finprod_congr fun i => finprod_congr_Prop rfl (h₁ i)

@[to_additive]
/-
**finprod_eq_one_of_forall_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_eq_one_of_forall_eq_one {f : α -> M} (h : forall x, f x = 1) : ∏ᶠ 
i, f i = 1
参数：h : forall x, f x = 1。
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
· 使用定理 `finprod_one`：finprod_one : (∏ᶠ _ : α, (1 : M)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finprod_eq_one_of_forall_eq_one {f : α → M} (h : ∀ x, f x = 1) : ∏ᶠ i, f i = 1 := by
  simp +contextual [h]

@[to_additive finsum_cond_pos]
/-
**one_lt_finprod_cond** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_lt_finprod_cond {M : Type*} [CommMonoid M] [PartialOrder M] [IsOrdered
CancelMonoid M] {f : ι -> M} {p : ι -> Prop} (h : forall i, p i -> 1 <= f i) (h'
 : exists i, p i ∧ 1 < f i) (hf : (mulSupport f inter {i | p i}).Finite) : 1 < ∏
ᶠ (i) (_ : p i), f i
参数：h : forall i, p i -> 1 <= f i；h' : exists i, p i ∧ 1 < f i；hf : (mulSupport f
 inter {i | p i}).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_cond_eq_prod_of_cond_iff`：finprod_cond_eq_prod_of_cond_iff (f : 
α -> M) {p : α -> Prop} {t : Finset α} (h : forall {x}, f x != 1 -> (p x ↔ x in 
t)) : (∏ᶠ (i) (_ : p i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.one_lt_prod'`：one_lt_prod' [MulLeftStrictMono M] (h : forall i in
 s, 1 <= f i) (hs : exists i in s, 1 < f i) : 1 < ∏ i in s, f i
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
-/
theorem one_lt_finprod_cond {M : Type*} [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M]
    {f : ι → M} {p : ι → Prop} (h : ∀ i, p i → 1 ≤ f i) (h' : ∃ i, p i ∧ 1 < f i)
    (hf : (mulSupport f ∩ {i | p i}).Finite) : 1 < ∏ᶠ (i) (_ : p i), f i := by
  rw [finprod_cond_eq_prod_of_cond_iff (t := hf.toFinset)]
  · apply Finset.one_lt_prod'
    · simp +contextual [h]
    · aesop
  · simp +contextual

@[deprecated (since := "2026-01-06")] alias finprod_cond_pos := finsum_cond_pos

@[to_additive finsum_pos]
/-
**one_lt_finprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_lt_finprod {M : Type*} [CommMonoid M] [PartialOrder M] [IsOrderedCance
lMonoid M] {f : ι -> M} (h : forall i, 1 <= f i) (h' : exists i, 1 < f i) (hf : 
HasFiniteMulSupport f) : 1 < ∏ᶠ i, f i
参数：h : forall i, 1 <= f i；h' : exists i, 1 < f i；hf : HasFiniteMulSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_mem_univ`：finprod_mem_univ (f : α -> M) : ∏ᶠ i in @Set.univ α, f
 i = ∏ᶠ i : α, f i
· 使用定理 `one_lt_finprod_cond`：one_lt_finprod_cond {M : Type*} [CommMonoid M] [Par
tialOrder M] [IsOrderedCancelMonoid M] {f : ι -> M} {p : ι -> Prop} (h : forall 
i, p i ->…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
theorem one_lt_finprod {M : Type*} [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M]
    {f : ι → M}
    (h : ∀ i, 1 ≤ f i) (h' : ∃ i, 1 < f i) (hf : HasFiniteMulSupport f) : 1 < ∏ᶠ i, f i := by
  rw [← finprod_mem_univ]
  apply one_lt_finprod_cond <;> simpa

@[deprecated (since := "2026-01-03")]
alias finsum_pos' := finsum_pos

@[to_additive existing finsum_pos', deprecated (since := "2026-01-03")]
alias one_lt_finprod' := one_lt_finprod

/-- Monotonicity of `finprod`. See `finprod_le_finprod` for a variant where
`M` is a `CommMonoidWithZero`. -/
@[to_additive /-- Monotonicity of `finsum.` -/]
/-
**finprod_le_finprod'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finprod_le_finprod' [PartialOrder M] [MulLeftMono M] (hf : HasFiniteMulSup
port f) (hg : HasFiniteMulSupport g) (h : f <= g) : ∏ᶠ a, f a <= ∏ᶠ a, g a
参数：hf : HasFiniteMulSupport f；hg : HasFiniteMulSupport g；h : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_finsetProd_of_mulSupport_subset`：finprod_eq_finsetProd_of_mul
Support_subset (f : α -> M) {s : Finset α} (h : mulSupport f subseteq (s : Set α
)) : ∏ᶠ i, f i = ∏ i in s, f i
· 使用定理 `Finset.prod_le_prod'`：prod_le_prod' [MulLeftMono N] (h : forall i in s, 
f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i

--- 原说明 ---
Monotonicity of `finprod`. See `finprod_le_finprod` for a variant where
`M` is a `CommMonoidWithZero`.
-/
lemma finprod_le_finprod' [PartialOrder M] [MulLeftMono M] (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) (h : f ≤ g) :
    ∏ᶠ a, f a ≤ ∏ᶠ a, g a := by
  have : Fintype ↑(f.mulSupport ∪ g.mulSupport) := (hf.union hg).fintype
  let s := (f.mulSupport ∪ g.mulSupport).toFinset
  rw [finprod_eq_finsetProd_of_mulSupport_subset f (show f.mulSupport ⊆ s by grind),
    finprod_eq_finsetProd_of_mulSupport_subset g (show g.mulSupport ⊆ s by grind)]
  exact Finset.prod_le_prod' fun i _ ↦ h i

/-- Monotonicity of `finprod`. See `finprod_le_finprod'` for a variant where
`M` is an ordered `CommMonoid`. -/
/-
**finprod_le_finprod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finprod_le_finprod {M : Type*} [CommMonoidWithZero M] [PartialOrder M] [Ze
roLEOneClass M] [PosMulMono M] {f g : α -> M} (hf : HasFiniteMulSupport f) (hf₀ 
: forall a, 0 <= f a) (hg : HasFiniteMulSupport g) (h : f <= g) : ∏ᶠ a, f a <= ∏
ᶠ a, g a
参数：hf : HasFiniteMulSupport f；hf₀ : forall a, 0 <= f a；hg : HasFiniteMulSupport 
g；h : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_finsetProd_of_mulSupport_subset`：finprod_eq_finsetProd_of_mul
Support_subset (f : α -> M) {s : Finset α} (h : mulSupport f subseteq (s : Set α
)) : ∏ᶠ i, f i = ∏ i in s, f i
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i

--- 原说明 ---
Monotonicity of `finprod`. See `finprod_le_finprod'` for a variant where
`M` is an ordered `CommMonoid`.
-/
lemma finprod_le_finprod {M : Type*} [CommMonoidWithZero M] [PartialOrder M] [ZeroLEOneClass M]
    [PosMulMono M] {f g : α → M} (hf : HasFiniteMulSupport f) (hf₀ : ∀ a, 0 ≤ f a)
    (hg : HasFiniteMulSupport g) (h : f ≤ g) :
    ∏ᶠ a, f a ≤ ∏ᶠ a, g a := by
  have : Fintype ↑(f.mulSupport ∪ g.mulSupport) := (hf.union hg).fintype
  let s := (f.mulSupport ∪ g.mulSupport).toFinset
  rw [finprod_eq_finsetProd_of_mulSupport_subset f (show f.mulSupport ⊆ s by grind),
    finprod_eq_finsetProd_of_mulSupport_subset g (show g.mulSupport ⊆ s by grind)]
  exact Finset.prod_le_prod (fun i _ ↦ hf₀ i) fun i _ ↦ h i
/-
**finprod_zero_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finprod_zero_le_one {M α : Type*} [CommMonoidWithZero M] [PartialOrder M] 
[ZeroLEOneClass M] [PosMulMono M] : ∏ᶠ _ : α, (0 : M) <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_one`：finprod_one : (∏ᶠ _ : α, (1 : M)) = 1
· 使用引理 `finprod_le_finprod`：finprod_le_finprod {M : Type*} [CommMonoidWithZero M
] [PartialOrder M] [ZeroLEOneClass M] [PosMulMono M] {f g : α -> M} (hf : HasFin
iteMulSu…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `Function.hasFiniteMulSupport_one`：hasFiniteMulSupport_one : HasFiniteMul
Support fun _ : α => (1 : M)
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `finprod_of_not_hasFiniteMulSupport`：finprod_of_not_hasFiniteMulSupport {
f : α -> M} (hf : ¬ f.HasFiniteMulSupport) : ∏ᶠ i, f i = 1
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
lemma finprod_zero_le_one {M α : Type*} [CommMonoidWithZero M] [PartialOrder M]
    [ZeroLEOneClass M] [PosMulMono M] :
    ∏ᶠ _ : α, (0 : M) ≤ 1 := by
  rw [← finprod_one (α := α)]
  by_cases H : (fun _ : α ↦ (0 : M)).HasFiniteMulSupport
  · exact finprod_le_finprod H (fun _ ↦ le_rfl) (by fun_prop) fun _ ↦ zero_le_one
  · rw [finprod_of_not_hasFiniteMulSupport H]
    exact finprod_one.symm.le

/-!
### Distributivity w.r.t. addition, subtraction, and (scalar) multiplication
-/


set_option backward.isDefEq.respectTransparency false in
/-- If the multiplicative supports of `f` and `g` are finite, then the product of `f i * g i` equals
the product of `f i` multiplied by the product of `g i`. -/
@[to_additive
      /-- If the additive supports of `f` and `g` are finite, then the sum of `f i + g i`
      equals the sum of `f i` plus the sum of `g i`. -/]
/-
**finprod_mul_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mul_distrib (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport
 g) : ∏ᶠ i, f i * g i = (∏ᶠ i, f i) * ∏ᶠ i, g i
参数：hf : HasFiniteMulSupport f；hg : HasFiniteMulSupport g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_prod_of_mulSupport_toFinset_subset`：finprod_eq_prod_of_mulSup
port_toFinset_subset (f : α -> M) (hf : HasFiniteMulSupport f) {s : Finset α} (h
 : hf.toFinset subseteq s) : ∏ᶠ i, …
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finprod_mul_distrib (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    ∏ᶠ i, f i * g i = (∏ᶠ i, f i) * ∏ᶠ i, g i := by
  classical
    rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf Finset.subset_union_left,
      finprod_eq_prod_of_mulSupport_toFinset_subset g hg Finset.subset_union_right, ←
      Finset.prod_mul_distrib]
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    simp only [Finset.coe_union, Finite.coe_toFinset, mulSupport_subset_iff,
      mem_union, mem_mulSupport]
    intro x
    contrapose!
    rintro ⟨hf, hg⟩
    simp [hf, hg]

/-- If the multiplicative supports of `f` and `g` are finite, then the product of `f i / g i`
equals the product of `f i` divided by the product of `g i`. -/
@[to_additive
      /-- If the additive supports of `f` and `g` are finite, then the sum of `f i - g i`
      equals the sum of `f i` minus the sum of `g i`. -/]
/-
**finprod_div_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_div_distrib [DivisionCommMonoid G] {f g : α -> G} (hf : HasFiniteM
ulSupport f) (hg : HasFiniteMulSupport g) : ∏ᶠ i, f i / g i = (∏ᶠ i, f i) / ∏ᶠ i
, g i
参数：hf : HasFiniteMulSupport f；hg : HasFiniteMulSupport g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `finprod_mul_distrib`：finprod_mul_distrib (hf : HasFiniteMulSupport f) (h
g : HasFiniteMulSupport g) : ∏ᶠ i, f i * g i = (∏ᶠ i, f i) * ∏ᶠ i, g i
· 使用定理 `Function.HasFiniteMulSupport.fun_inv`：∀ {α : Type u_1} {M : Type u_3} [i
nst : DivisionMonoid M] {f : α → M},   Function.HasFiniteMulSupport f → Function
.HasFiniteMulSupport fun i…
· 使用定理 `finprod_inv_distrib`：finprod_inv_distrib [DivisionCommMonoid G] (f : α -
> G) : (∏ᶠ x, (f x)⁻¹) = (∏ᶠ x, f x)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finprod_div_distrib [DivisionCommMonoid G] {f g : α → G} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) : ∏ᶠ i, f i / g i = (∏ᶠ i, f i) / ∏ᶠ i, g i := by
  simp only [div_eq_mul_inv, finprod_mul_distrib hf <| hg.fun_inv, finprod_inv_distrib]

/-- A more general version of `finprod_mem_mul_distrib` that only requires `s ∩ mulSupport f` and
`s ∩ mulSupport g` rather than `s` to be finite. -/
@[to_additive
      /-- A more general version of `finsum_mem_add_distrib` that only requires `s ∩ support f`
      and `s ∩ support g` rather than `s` to be finite. -/]
/-
**finprod_mem_mul_distrib'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_mul_distrib' (hf : (s inter mulSupport f).Finite) (hg : (s int
er mulSupport g).Finite) : ∏ᶠ i in s, f i * g i = (∏ᶠ i in s, f i) * ∏ᶠ i in s, 
g i
参数：hf : (s inter mulSupport f).Finite；hg : (s inter mulSupport g).Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_mem_def`：finprod_mem_def (s : Set α) (f : α -> M) : ∏ᶠ a in s, f
 a = ∏ᶠ a, mulIndicator s f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.mulIndicator_mul`：mulIndicator_mul (s : Set α) (f g : α -> M) : (mul
Indicator s fun a => f a * g a) = fun a => mulIndicator s f a * mulIndicator s g
 a
· 使用定理 `finprod_mul_distrib`：finprod_mul_distrib (hf : HasFiniteMulSupport f) (h
g : HasFiniteMulSupport g) : ∏ᶠ i, f i * g i = (∏ᶠ i, f i) * ∏ᶠ i, g i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.mulSupport_mulIndicator`：mulSupport_mulIndicator : Function.mulSuppo
rt (s.mulIndicator f) = s inter Function.mulSupport f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finprod_mem_mul_distrib' (hf : (s ∩ mulSupport f).Finite) (hg : (s ∩ mulSupport g).Finite) :
    ∏ᶠ i ∈ s, f i * g i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ s, g i := by
  rw [← mulSupport_mulIndicator] at hf hg
  simp only [finprod_mem_def, mulIndicator_mul, finprod_mul_distrib hf hg]

/-- The product of the constant function `1` over any set equals `1`. -/
@[to_additive /-- The sum of the constant function `0` over any set equals `0`. -/]
/-
**finprod_mem_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_one (s : Set α) : (∏ᶠ i in s, (1 : M)) = 1
参数：s : Set α。
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
· 使用定理 `finprod_one`：finprod_one : (∏ᶠ _ : α, (1 : M)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The product of the constant function `1` over any set equals `1`.
-/
theorem finprod_mem_one (s : Set α) : (∏ᶠ i ∈ s, (1 : M)) = 1 := by simp

/-- If a function `f` equals `1` on a set `s`, then the product of `f i` over `i ∈ s` equals `1`. -/
@[to_additive
      /-- If a function `f` equals `0` on a set `s`, then the sum of `f i` over `i ∈ s`
      equals `0`. -/]
/-
**finprod_mem_of_eqOn_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_of_eqOn_one (hf : s.EqOn f 1) : ∏ᶠ i in s, f i = 1
参数：hf : s.EqOn f 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_mem_one`：finprod_mem_one (s : Set α) : (∏ᶠ i in s, (1 : M)) = 1
· 使用定理 `finprod_mem_congr`：finprod_mem_congr (h₀ : s = t) (h₁ : forall x in t, f
 x = g x) : ∏ᶠ i in s, f i = ∏ᶠ i in t, g i
-/
theorem finprod_mem_of_eqOn_one (hf : s.EqOn f 1) : ∏ᶠ i ∈ s, f i = 1 := by
  rw [← finprod_mem_one s]
  exact finprod_mem_congr rfl hf

/-- If the product of `f i` over `i ∈ s` is not equal to `1`, then there is some `x ∈ s` such that
`f x ≠ 1`. -/
@[to_additive
      /-- If the sum of `f i` over `i ∈ s` is not equal to `0`, then there is some `x ∈ s`
      such that `f x ≠ 0`. -/]
/-
**exists_ne_one_of_finprod_mem_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_ne_one_of_finprod_mem_ne_one (h : ∏ᶠ i in s, f i != 1) : exists x i
n s, f x != 1
参数：h : ∏ᶠ i in s, f i != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `finprod_mem_of_eqOn_one`：finprod_mem_of_eqOn_one (hf : s.EqOn f 1) : ∏ᶠ 
i in s, f i = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem exists_ne_one_of_finprod_mem_ne_one (h : ∏ᶠ i ∈ s, f i ≠ 1) : ∃ x ∈ s, f x ≠ 1 := by
  by_contra! h'
  exact h (finprod_mem_of_eqOn_one h')

/-- Given a finite set `s`, the product of `f i * g i` over `i ∈ s` equals the product of `f i`
over `i ∈ s` times the product of `g i` over `i ∈ s`. -/
@[to_additive
      /-- Given a finite set `s`, the sum of `f i + g i` over `i ∈ s` equals the sum of `f i`
      over `i ∈ s` plus the sum of `g i` over `i ∈ s`. -/]
/-
**finprod_mem_mul_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_mul_distrib (hs : s.Finite) : ∏ᶠ i in s, f i * g i = (∏ᶠ i in 
s, f i) * ∏ᶠ i in s, g i
参数：hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_mul_distrib'`：finprod_mem_mul_distrib' (hf : (s inter mulSup
port f).Finite) (hg : (s inter mulSupport g).Finite) : ∏ᶠ i in s, f i * g i = (∏
ᶠ i in s, f i)…
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
-/
theorem finprod_mem_mul_distrib (hs : s.Finite) :
    ∏ᶠ i ∈ s, f i * g i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ s, g i :=
  finprod_mem_mul_distrib' (hs.inter_of_left _) (hs.inter_of_left _)

@[to_additive]
/-
**MonoidHom.map_finprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.map_finprod {f : α -> M} (g : M ->* N) (hf : HasFiniteMulSupport
 f) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i)
参数：g : M ->* N；hf : HasFiniteMulSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_finprod_plift`：MonoidHom.map_finprod_plift (f : M ->* N) (
g : α -> M) (h : HasFiniteMulSupport <| g ∘ PLift.down) : f (∏ᶠ x, g x) = ∏ᶠ x, 
f (g x)
· 使用定理 `Set.Finite.preimage`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}
, Set.InjOn f (f ⁻¹' s) → s.Finite → (f ⁻¹' s).Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem MonoidHom.map_finprod {f : α → M} (g : M →* N) (hf : HasFiniteMulSupport f) :
    g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  g.map_finprod_plift f <| hf.preimage Equiv.plift.injective.injOn

@[to_additive]
/-
**map_finprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_finprod {G : Type*} [FunLike G M N] [MonoidHomClass G M N] (g : G) (hf
 : HasFiniteMulSupport f) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i)
参数：g : G；hf : HasFiniteMulSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_finprod`：MonoidHom.map_finprod {f : α -> M} (g : M ->* N) 
(hf : HasFiniteMulSupport f) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i)
-/
theorem map_finprod {G : Type*} [FunLike G M N] [MonoidHomClass G M N] (g : G)
    (hf : HasFiniteMulSupport f) :
    g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  (g : M →* N).map_finprod hf

@[to_additive]
/-
**finprod_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_pow (hf : HasFiniteMulSupport f) (n : Nat) : (∏ᶠ i, f i) ^ n = ∏ᶠ 
i, f i ^ n
参数：hf : HasFiniteMulSupport f；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_finprod`：MonoidHom.map_finprod {f : α -> M} (g : M ->* N) 
(hf : HasFiniteMulSupport f) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i)
-/
theorem finprod_pow (hf : HasFiniteMulSupport f) (n : ℕ) : (∏ᶠ i, f i) ^ n = ∏ᶠ i, f i ^ n :=
  (powMonoidHom n).map_finprod hf

/-- See also `finsum_smul` for a version that works even when the support of `f` is not finite,
but with slightly stronger typeclass requirements. -/
/-
**finsum_smul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsum_smul' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {f 
: ι -> R} (hf : HasFiniteSupport f) (x : M) : (∑ᶠ i, f i) • x = ∑ᶠ i, f i • x
参数：hf : HasFiniteSupport f；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_finsum`：∀ {α : Type u_1} {M : Type u_5} {N : Type u_6} 
[inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] {f : α → M}   (g : M →+ N), 
Function.HasF…

--- 原说明 ---
See also `finsum_smul` for a version that works even when the support of `f` is 
not finite,
but with slightly stronger typeclass requirements.
-/
theorem finsum_smul' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {f : ι → R}
    (hf : HasFiniteSupport f) (x : M) : (∑ᶠ i, f i) • x = ∑ᶠ i, f i • x :=
  ((smulAddHom R M).flip x).map_finsum hf

/-- See also `smul_finsum` for a version that works even when the support of `f` is not finite,
but with slightly stronger typeclass requirements. -/
/-
**smul_finsum'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_finsum' {R M : Type*} [AddCommMonoid M] [DistribSMul R M] (c : R) {f 
: ι -> M} (hf : HasFiniteSupport f) : (c • ∑ᶠ i, f i) = ∑ᶠ i, c • f i
参数：c : R；hf : HasFiniteSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_finsum`：∀ {α : Type u_1} {M : Type u_5} {N : Type u_6} 
[inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] {f : α → M}   (g : M →+ N), 
Function.HasF…

--- 原说明 ---
See also `smul_finsum` for a version that works even when the support of `f` is 
not finite,
but with slightly stronger typeclass requirements.
-/
theorem smul_finsum' {R M : Type*} [AddCommMonoid M] [DistribSMul R M] (c : R)
    {f : ι → M} (hf : HasFiniteSupport f) : (c • ∑ᶠ i, f i) = ∑ᶠ i, c • f i :=
  (DistribSMul.toAddMonoidHom M c).map_finsum hf

/-- A more general version of `MonoidHom.map_finprod_mem` that requires `s ∩ mulSupport f` rather
than `s` to be finite. -/
@[to_additive
      /-- A more general version of `AddMonoidHom.map_finsum_mem` that requires
      `s ∩ support f` rather than `s` to be finite. -/]
/-
**MonoidHom.map_finprod_mem'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.map_finprod_mem' {f : α -> M} (g : M ->* N) (h₀ : (s inter mulSu
pport f).Finite) : g (∏ᶠ j in s, f j) = ∏ᶠ i in s, g (f i)
参数：g : M ->* N；h₀ : (s inter mulSupport f).Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.map_finprod`：MonoidHom.map_finprod {f : α -> M} (g : M ->* N) 
(hf : HasFiniteMulSupport f) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finprod_eq_mulIndicator_apply`：finprod_eq_mulIndicator_apply (s : Set α)
 (f : α -> M) (a : α) : ∏ᶠ _ : a in s, f a = mulIndicator s f a
· 使用引理 `Set.mulSupport_mulIndicator`：mulSupport_mulIndicator : Function.mulSuppo
rt (s.mulIndicator f) = s inter Function.mulSupport f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidHom.map_finprod_Prop`：MonoidHom.map_finprod_Prop {p : Prop} (f : M
 ->* N) (g : p -> M) : f (∏ᶠ x, g x) = ∏ᶠ x, f (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem MonoidHom.map_finprod_mem' {f : α → M} (g : M →* N) (h₀ : (s ∩ mulSupport f).Finite) :
    g (∏ᶠ j ∈ s, f j) = ∏ᶠ i ∈ s, g (f i) := by
  rw [g.map_finprod]
  · simp only [g.map_finprod_Prop]
  · simpa only [finprod_eq_mulIndicator_apply, HasFiniteMulSupport, mulSupport_mulIndicator]

/-- Given a monoid homomorphism `g : M →* N` and a function `f : α → M`, the value of `g` at the
product of `f i` over `i ∈ s` equals the product of `g (f i)` over `s`. -/
@[to_additive
      /-- Given an additive monoid homomorphism `g : M →* N` and a function `f : α → M`, the
      value of `g` at the sum of `f i` over `i ∈ s` equals the sum of `g (f i)` over `s`. -/]
/-
**MonoidHom.map_finprod_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.map_finprod_mem (f : α -> M) (g : M ->* N) (hs : s.Finite) : g (
∏ᶠ j in s, f j) = ∏ᶠ i in s, g (f i)
参数：f : α -> M；g : M ->* N；hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_finprod_mem'`：MonoidHom.map_finprod_mem' {f : α -> M} (g :
 M ->* N) (h₀ : (s inter mulSupport f).Finite) : g (∏ᶠ j in s, f j) = ∏ᶠ i in s,
 g (f i)
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
-/
theorem MonoidHom.map_finprod_mem (f : α → M) (g : M →* N) (hs : s.Finite) :
    g (∏ᶠ j ∈ s, f j) = ∏ᶠ i ∈ s, g (f i) :=
  g.map_finprod_mem' (hs.inter_of_left _)

@[to_additive]
/-
**MulEquiv.map_finprod_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulEquiv.map_finprod_mem (g : M ≃* N) (f : α -> M) {s : Set α} (hs : s.Fin
ite) : g (∏ᶠ i in s, f i) = ∏ᶠ i in s, g (f i)
参数：g : M ≃* N；f : α -> M；hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_finprod_mem`：MonoidHom.map_finprod_mem (f : α -> M) (g : M
 ->* N) (hs : s.Finite) : g (∏ᶠ j in s, f j) = ∏ᶠ i in s, g (f i)
-/
theorem MulEquiv.map_finprod_mem (g : M ≃* N) (f : α → M) {s : Set α} (hs : s.Finite) :
    g (∏ᶠ i ∈ s, f i) = ∏ᶠ i ∈ s, g (f i) :=
  g.toMonoidHom.map_finprod_mem f hs

@[to_additive]
/-
**finprod_mem_inv_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_inv_distrib [DivisionCommMonoid G] (f : α -> G) (hs : s.Finite
) : (∏ᶠ x in s, (f x)⁻¹) = (∏ᶠ x in s, f x)⁻¹
参数：f : α -> G；hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulEquiv.map_finprod_mem`：MulEquiv.map_finprod_mem (g : M ≃* N) (f : α -
> M) {s : Set α} (hs : s.Finite) : g (∏ᶠ i in s, f i) = ∏ᶠ i in s, g (f i)
-/
theorem finprod_mem_inv_distrib [DivisionCommMonoid G] (f : α → G) (hs : s.Finite) :
    (∏ᶠ x ∈ s, (f x)⁻¹) = (∏ᶠ x ∈ s, f x)⁻¹ :=
  ((MulEquiv.inv G).map_finprod_mem f hs).symm

/-- Given a finite set `s`, the product of `f i / g i` over `i ∈ s` equals the product of `f i`
over `i ∈ s` divided by the product of `g i` over `i ∈ s`. -/
@[to_additive
      /-- Given a finite set `s`, the sum of `f i / g i` over `i ∈ s` equals the sum of `f i`
      over `i ∈ s` minus the sum of `g i` over `i ∈ s`. -/]
/-
**finprod_mem_div_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_div_distrib [DivisionCommMonoid G] (f g : α -> G) (hs : s.Fini
te) : ∏ᶠ i in s, f i / g i = (∏ᶠ i in s, f i) / ∏ᶠ i in s, g i
参数：f g : α -> G；hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finprod_congr_Prop`：finprod_congr_Prop {p q : Prop} {f : p -> M} {g : q 
-> M} (hpq : p = q) (hfg : forall h : q, f (hpq.mpr h) = g h) : finprod f = finp
rod g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `finprod_mem_mul_distrib`：finprod_mem_mul_distrib (hs : s.Finite) : ∏ᶠ i 
in s, f i * g i = (∏ᶠ i in s, f i) * ∏ᶠ i in s, g i
· 使用定理 `finprod_mem_inv_distrib`：finprod_mem_inv_distrib [DivisionCommMonoid G] 
(f : α -> G) (hs : s.Finite) : (∏ᶠ x in s, (f x)⁻¹) = (∏ᶠ x in s, f x)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finprod_mem_div_distrib [DivisionCommMonoid G] (f g : α → G) (hs : s.Finite) :
    ∏ᶠ i ∈ s, f i / g i = (∏ᶠ i ∈ s, f i) / ∏ᶠ i ∈ s, g i := by
  simp only [div_eq_mul_inv, finprod_mem_mul_distrib hs, finprod_mem_inv_distrib g hs]

/-!
### `∏ᶠ x ∈ s, f x` and set operations
-/


/-- The product of any function over an empty set is `1`. -/
@[to_additive /-- The sum of any function over an empty set is `0`. -/]
/-
**finprod_mem_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_empty : (∏ᶠ i in (∅ : Set α), f i) = 1
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
· 使用定理 `finprod_congr_Prop`：finprod_congr_Prop {p q : Prop} {f : p -> M} {g : q 
-> M} (hpq : p = q) (hfg : forall h : q, f (hpq.mpr h) = g h) : finprod f = finp
rod g
· 使用定理 `finprod_false`：finprod_false (f : False -> M) : ∏ᶠ i, f i = 1
· 使用定理 `finprod_one`：finprod_one : (∏ᶠ _ : α, (1 : M)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The product of any function over an empty set is `1`.
-/
theorem finprod_mem_empty : (∏ᶠ i ∈ (∅ : Set α), f i) = 1 := by simp

/-- A set `s` is nonempty if the product of some function over `s` is not equal to `1`. -/
@[to_additive
/-- A set `s` is nonempty if the sum of some function over `s` is not equal to `0`. -/]
/-
**nonempty_of_finprod_mem_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_of_finprod_mem_ne_one (h : ∏ᶠ i in s, f i != 1) : s.Nonempty
参数：h : ∏ᶠ i in s, f i != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `finprod_mem_empty`：finprod_mem_empty : (∏ᶠ i in (∅ : Set α), f i) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nonempty_of_finprod_mem_ne_one (h : ∏ᶠ i ∈ s, f i ≠ 1) : s.Nonempty :=
  nonempty_iff_ne_empty.2 fun h' => h <| h'.symm ▸ finprod_mem_empty

/-- Given finite sets `s` and `t`, the product of `f i` over `i ∈ s ∪ t` times the product of
`f i` over `i ∈ s ∩ t` equals the product of `f i` over `i ∈ s` times the product of `f i`
over `i ∈ t`. -/
@[to_additive
      /-- Given finite sets `s` and `t`, the sum of `f i` over `i ∈ s ∪ t` plus the sum of
      `f i` over `i ∈ s ∩ t` equals the sum of `f i` over `i ∈ s` plus the sum of `f i`
      over `i ∈ t`. -/]
/-
**finprod_mem_union_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_union_inter (hs : s.Finite) (ht : t.Finite) : ((∏ᶠ i in s unio
n t, f i) * ∏ᶠ i in s inter t, f i) = (∏ᶠ i in s, f i) * ∏ᶠ i in t, f i
参数：hs : s.Finite；ht : t.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Finset.coe_inter`：coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ in
ter s₂ : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `finprod_mem_coe_finset`：finprod_mem_coe_finset (f : α -> M) (s : Finset 
α) : (∏ᶠ i in (s : Set α), f i) = ∏ i in s, f i
· 使用定理 `Finset.prod_union_inter`：prod_union_inter [DecidableEq ι] : (∏ x in s₁ u
nion s₂, f x) * ∏ x in s₁ inter s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finprod_mem_union_inter (hs : s.Finite) (ht : t.Finite) :
    ((∏ᶠ i ∈ s ∪ t, f i) * ∏ᶠ i ∈ s ∩ t, f i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i := by
  lift s to Finset α using hs; lift t to Finset α using ht
  classical
    rw [← Finset.coe_union, ← Finset.coe_inter]
    simp only [finprod_mem_coe_finset, Finset.prod_union_inter]

/-- A more general version of `finprod_mem_union_inter` that requires `s ∩ mulSupport f` and
`t ∩ mulSupport f` rather than `s` and `t` to be finite. -/
@[to_additive
      /-- A more general version of `finsum_mem_union_inter` that requires `s ∩ support f` and
      `t ∩ support f` rather than `s` and `t` to be finite. -/]
/-
**finprod_mem_union_inter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_union_inter' (hs : (s inter mulSupport f).Finite) (ht : (t int
er mulSupport f).Finite) : ((∏ᶠ i in s union t, f i) * ∏ᶠ i in s inter t, f i) =
 (∏ᶠ i in s, f i) * ∏ᶠ i in t, f i
参数：hs : (s inter mulSupport f).Finite；ht : (t inter mulSupport f).Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_mem_inter_mulSupport`：finprod_mem_inter_mulSupport (f : α -> M) 
(s : Set α) : ∏ᶠ i in s inter mulSupport f, f i = ∏ᶠ i in s, f i
· 使用定理 `finprod_mem_union_inter`：finprod_mem_union_inter (hs : s.Finite) (ht : t
.Finite) : ((∏ᶠ i in s union t, f i) * ∏ᶠ i in s inter t, f i) = (∏ᶠ i in s, f i
) * ∏ᶠ i in t…
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
· 使用定理 `Set.inter_left_comm`：inter_left_comm (s₁ s₂ s₃ : Set α) : s₁ inter (s₂ i
nter s₃) = s₂ inter (s₁ inter s₃)
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
-/
theorem finprod_mem_union_inter' (hs : (s ∩ mulSupport f).Finite) (ht : (t ∩ mulSupport f).Finite) :
    ((∏ᶠ i ∈ s ∪ t, f i) * ∏ᶠ i ∈ s ∩ t, f i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mulSupport f s, ← finprod_mem_inter_mulSupport f t, ←
    finprod_mem_union_inter hs ht, ← union_inter_distrib_right, finprod_mem_inter_mulSupport, ←
    finprod_mem_inter_mulSupport f (s ∩ t)]
  rw [inter_left_comm, inter_assoc, inter_assoc, inter_self, inter_left_comm]

/-- A more general version of `finprod_mem_union` that requires `s ∩ mulSupport f` and
`t ∩ mulSupport f` rather than `s` and `t` to be finite. -/
@[to_additive
      /-- A more general version of `finsum_mem_union` that requires `s ∩ support f` and
      `t ∩ support f` rather than `s` and `t` to be finite. -/]
/-
**finprod_mem_union'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_union' (hst : Disjoint s t) (hs : (s inter mulSupport f).Finit
e) (ht : (t inter mulSupport f).Finite) : ∏ᶠ i in s union t, f i = (∏ᶠ i in s, f
 i) * ∏ᶠ i in t, f i
参数：hst : Disjoint s t；hs : (s inter mulSupport f).Finite；ht : (t inter mulSuppor
t f).Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_mem_union_inter'`：finprod_mem_union_inter' (hs : (s inter mulSup
port f).Finite) (ht : (t inter mulSupport f).Finite) : ((∏ᶠ i in s union t, f i)
 * ∏ᶠ i in s i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `finprod_mem_empty`：finprod_mem_empty : (∏ᶠ i in (∅ : Set α), f i) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem finprod_mem_union' (hst : Disjoint s t) (hs : (s ∩ mulSupport f).Finite)
    (ht : (t ∩ mulSupport f).Finite) : ∏ᶠ i ∈ s ∪ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_union_inter' hs ht, disjoint_iff_inter_eq_empty.1 hst, finprod_mem_empty,
    mul_one]

/-- Given two finite disjoint sets `s` and `t`, the product of `f i` over `i ∈ s ∪ t` equals the
product of `f i` over `i ∈ s` times the product of `f i` over `i ∈ t`. -/
@[to_additive
      /-- Given two finite disjoint sets `s` and `t`, the sum of `f i` over `i ∈ s ∪ t` equals
      the sum of `f i` over `i ∈ s` plus the sum of `f i` over `i ∈ t`. -/]
/-
**finprod_mem_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_union (hst : Disjoint s t) (hs : s.Finite) (ht : t.Finite) : ∏
ᶠ i in s union t, f i = (∏ᶠ i in s, f i) * ∏ᶠ i in t, f i
参数：hst : Disjoint s t；hs : s.Finite；ht : t.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_union'`：finprod_mem_union' (hst : Disjoint s t) (hs : (s int
er mulSupport f).Finite) (ht : (t inter mulSupport f).Finite) : ∏ᶠ i in s union 
t, f i =…
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
-/
theorem finprod_mem_union (hst : Disjoint s t) (hs : s.Finite) (ht : t.Finite) :
    ∏ᶠ i ∈ s ∪ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i :=
  finprod_mem_union' hst (hs.inter_of_left _) (ht.inter_of_left _)

/-- A more general version of `finprod_mem_union'` that requires `s ∩ mulSupport f` and
`t ∩ mulSupport f` rather than `s` and `t` to be disjoint -/
@[to_additive
      /-- A more general version of `finsum_mem_union'` that requires `s ∩ support f` and
      `t ∩ support f` rather than `s` and `t` to be disjoint -/]
/-
**finprod_mem_union''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_union'' (hst : Disjoint (s inter mulSupport f) (t inter mulSup
port f)) (hs : (s inter mulSupport f).Finite) (ht : (t inter mulSupport f).Finit
e) : ∏ᶠ i in s union t, f i = (∏ᶠ i in s, f i) * ∏ᶠ i in t, f i
参数：hst : Disjoint (s inter mulSupport f) (t inter mulSupport f)；hs : (s inter mu
lSupport f).Finite；ht : (t inter mulSupport f).Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_mem_inter_mulSupport`：finprod_mem_inter_mulSupport (f : α -> M) 
(s : Set α) : ∏ᶠ i in s inter mulSupport f, f i = ∏ᶠ i in s, f i
· 使用定理 `finprod_mem_union`：finprod_mem_union (hst : Disjoint s t) (hs : s.Finite
) (ht : t.Finite) : ∏ᶠ i in s union t, f i = (∏ᶠ i in s, f i) * ∏ᶠ i in t, f i
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
-/
theorem finprod_mem_union'' (hst : Disjoint (s ∩ mulSupport f) (t ∩ mulSupport f))
    (hs : (s ∩ mulSupport f).Finite) (ht : (t ∩ mulSupport f).Finite) :
    ∏ᶠ i ∈ s ∪ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mulSupport f s, ← finprod_mem_inter_mulSupport f t, ←
    finprod_mem_union hst hs ht, ← union_inter_distrib_right, finprod_mem_inter_mulSupport]

/-- The product of `f i` over `i ∈ {a}` equals `f a`. -/
@[to_additive /-- The sum of `f i` over `i ∈ {a}` equals `f a`. -/]
/-
**finprod_mem_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_singleton : (∏ᶠ i in ({a} : Set α), f i) = f a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `finprod_mem_coe_finset`：finprod_mem_coe_finset (f : α -> M) (s : Finset 
α) : (∏ᶠ i in (s : Set α), f i) = ∏ i in s, f i
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a

--- 原说明 ---
The product of `f i` over `i ∈ {a}` equals `f a`.
-/
theorem finprod_mem_singleton : (∏ᶠ i ∈ ({a} : Set α), f i) = f a := by
  rw [← Finset.coe_singleton, finprod_mem_coe_finset, Finset.prod_singleton]

@[to_additive (attr := simp)]
/-
**finprod_cond_eq_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_cond_eq_left : (∏ᶠ (i) (_ : i = a), f i) = f a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_singleton`：finprod_mem_singleton : (∏ᶠ i in ({a} : Set α), f
 i) = f a
-/
theorem finprod_cond_eq_left : (∏ᶠ (i) (_ : i = a), f i) = f a :=
  finprod_mem_singleton

@[to_additive (attr := simp)]
/-
**finprod_cond_eq_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_cond_eq_right : (∏ᶠ (i) (_ : a = i), f i) = f a
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
· 使用定理 `finprod_congr_Prop`：finprod_congr_Prop {p q : Prop} {f : p -> M} {g : q 
-> M} (hpq : p = q) (hfg : forall h : q, f (hpq.mpr h) = g h) : finprod f = finp
rod g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `finprod_cond_eq_left`：finprod_cond_eq_left : (∏ᶠ (i) (_ : i = a), f i) =
 f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finprod_cond_eq_right : (∏ᶠ (i) (_ : a = i), f i) = f a := by simp [@eq_comm _ a]

/-- A more general version of `finprod_mem_insert` that requires `s ∩ mulSupport f` rather than `s`
to be finite. -/
@[to_additive
      /-- A more general version of `finsum_mem_insert` that requires `s ∩ support f` rather
      than `s` to be finite. -/]
/-
**finprod_mem_insert'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_insert' (f : α -> M) (h : a ∉ s) (hs : (s inter mulSupport f).
Finite) : ∏ᶠ i in insert a s, f i = f a * ∏ᶠ i in s, f i
参数：f : α -> M；h : a ∉ s；hs : (s inter mulSupport f).Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `finprod_mem_union'`：finprod_mem_union' (hst : Disjoint s t) (hs : (s int
er mulSupport f).Finite) (ht : (t inter mulSupport f).Finite) : ∏ᶠ i in s union 
t, f i =…
· 使用引理 `Set.disjoint_singleton_left`：disjoint_singleton_left : Disjoint {a} s ↔ 
a ∉ s
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `finprod_mem_singleton`：finprod_mem_singleton : (∏ᶠ i in ({a} : Set α), f
 i) = f a
-/
theorem finprod_mem_insert' (f : α → M) (h : a ∉ s) (hs : (s ∩ mulSupport f).Finite) :
    ∏ᶠ i ∈ insert a s, f i = f a * ∏ᶠ i ∈ s, f i := by
  rw [insert_eq, finprod_mem_union' _ _ hs, finprod_mem_singleton]
  · rwa [disjoint_singleton_left]
  · exact (finite_singleton a).inter_of_left _

/-- Given a finite set `s` and an element `a ∉ s`, the product of `f i` over `i ∈ insert a s` equals
`f a` times the product of `f i` over `i ∈ s`. -/
@[to_additive
      /-- Given a finite set `s` and an element `a ∉ s`, the sum of `f i` over `i ∈ insert a s`
      equals `f a` plus the sum of `f i` over `i ∈ s`. -/]
/-
**finprod_mem_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_insert (f : α -> M) (h : a ∉ s) (hs : s.Finite) : ∏ᶠ i in inse
rt a s, f i = f a * ∏ᶠ i in s, f i
参数：f : α -> M；h : a ∉ s；hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_insert'`：finprod_mem_insert' (f : α -> M) (h : a ∉ s) (hs : 
(s inter mulSupport f).Finite) : ∏ᶠ i in insert a s, f i = f a * ∏ᶠ i in s, f i
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
-/
theorem finprod_mem_insert (f : α → M) (h : a ∉ s) (hs : s.Finite) :
    ∏ᶠ i ∈ insert a s, f i = f a * ∏ᶠ i ∈ s, f i :=
  finprod_mem_insert' f h <| hs.inter_of_left _

/-- If `f a = 1` when `a ∉ s`, then the product of `f i` over `i ∈ insert a s` equals the product of
`f i` over `i ∈ s`. -/
@[to_additive
      /-- If `f a = 0` when `a ∉ s`, then the sum of `f i` over `i ∈ insert a s` equals the sum
      of `f i` over `i ∈ s`. -/]
/-
**finprod_mem_insert_of_eq_one_if_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_insert_of_eq_one_if_notMem (h : a ∉ s -> f a = 1) : ∏ᶠ i in in
sert a s, f i = ∏ᶠ i in s, f i
参数：h : a ∉ s -> f a = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_inter_mulSupport_eq'`：finprod_mem_inter_mulSupport_eq' (f : 
α -> M) (s t : Set α) (h : forall x in mulSupport f, x in s ↔ x in t) : ∏ᶠ i in 
s, f i = ∏ᶠ i in t, f …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
-/
theorem finprod_mem_insert_of_eq_one_if_notMem (h : a ∉ s → f a = 1) :
    ∏ᶠ i ∈ insert a s, f i = ∏ᶠ i ∈ s, f i := by
  refine finprod_mem_inter_mulSupport_eq' _ _ _ fun x hx => ⟨?_, Or.inr⟩
  rintro (rfl | hxs)
  exacts [not_imp_comm.1 h hx, hxs]

/-- If `f a = 1`, then the product of `f i` over `i ∈ insert a s` equals the product of `f i` over
`i ∈ s`. -/
@[to_additive
      /-- If `f a = 0`, then the sum of `f i` over `i ∈ insert a s` equals the sum of `f i`
      over `i ∈ s`. -/]
/-
**finprod_mem_insert_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_insert_one (h : f a = 1) : ∏ᶠ i in insert a s, f i = ∏ᶠ i in s
, f i
参数：h : f a = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_insert_of_eq_one_if_notMem`：finprod_mem_insert_of_eq_one_if_
notMem (h : a ∉ s -> f a = 1) : ∏ᶠ i in insert a s, f i = ∏ᶠ i in s, f i
-/
theorem finprod_mem_insert_one (h : f a = 1) : ∏ᶠ i ∈ insert a s, f i = ∏ᶠ i ∈ s, f i :=
  finprod_mem_insert_of_eq_one_if_notMem fun _ => h

/-- If the multiplicative support of `f` is finite, then for every `x` in the domain of `f`, `f x`
divides `finprod f`. -/
/-
**finprod_mem_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_dvd {f : α -> N} (a : α) (hf : HasFiniteMulSupport f) : f a ∣ 
finprod f
参数：a : α；hf : HasFiniteMulSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_prod_of_mulSupport_toFinset_subset`：finprod_eq_prod_of_mulSup
port_toFinset_subset (f : α -> M) (hf : HasFiniteMulSupport f) {s : Finset α} (h
 : hf.toFinset subseteq s) : ∏ᶠ i, …
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Function.notMem_mulSupport`：notMem_mulSupport : x ∉ mulSupport f ↔ f x =
 1
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a

--- 原说明 ---
If the multiplicative support of `f` is finite, then for every `x` in the domain
 of `f`, `f x`
divides `finprod f`.
-/
theorem finprod_mem_dvd {f : α → N} (a : α) (hf : HasFiniteMulSupport f) : f a ∣ finprod f := by
  by_cases ha : a ∈ mulSupport f
  · rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf (Set.Subset.refl _)]
    exact Finset.dvd_prod_of_mem f ((Finite.mem_toFinset hf).mpr ha)
  · rw [notMem_mulSupport.mp ha]
    exact one_dvd (finprod f)

/-- The product of `f i` over `i ∈ {a, b}`, `a ≠ b`, is equal to `f a * f b`. -/
@[to_additive /-- The sum of `f i` over `i ∈ {a, b}`, `a ≠ b`, is equal to `f a + f b`. -/]
/-
**finprod_mem_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_pair (h : a != b) : (∏ᶠ i in ({a, b} : Set α), f i) = f a * f 
b
参数：h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_mem_insert`：finprod_mem_insert (f : α -> M) (h : a ∉ s) (hs : s.
Finite) : ∏ᶠ i in insert a s, f i = f a * ∏ᶠ i in s, f i
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `finprod_mem_singleton`：finprod_mem_singleton : (∏ᶠ i in ({a} : Set α), f
 i) = f a

--- 原说明 ---
The product of `f i` over `i ∈ {a, b}`, `a ≠ b`, is equal to `f a * f b`.
-/
theorem finprod_mem_pair (h : a ≠ b) : (∏ᶠ i ∈ ({a, b} : Set α), f i) = f a * f b := by
  rw [finprod_mem_insert, finprod_mem_singleton]
  exacts [h, finite_singleton b]

set_option backward.isDefEq.respectTransparency false in
/-- The product of `f y` over `y ∈ g '' s` equals the product of `f (g i)` over `s`
provided that `g` is injective on `s ∩ mulSupport (f ∘ g)`. -/
@[to_additive
      /-- The sum of `f y` over `y ∈ g '' s` equals the sum of `f (g i)` over `s` provided that
      `g` is injective on `s ∩ support (f ∘ g)`. -/]
/-
**finprod_mem_image'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_image' {s : Set β} {g : β -> α} (hg : (s inter mulSupport (f ∘
 g)).InjOn g) : ∏ᶠ i in g '' s, f i = ∏ᶠ j in s, f (g j)
参数：hg : (s inter mulSupport (f ∘ g)).InjOn g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `finprod_mem_eq_prod`：finprod_mem_eq_prod (f : α -> M) {s : Set α} (hf : 
(s inter mulSupport f).Finite) : ∏ᶠ i in s, f i = ∏ i in hf.toFinset, f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_image`：prod_image [DecidableEq ι] {s : Finset κ} {g : κ -> ι
} : Set.InjOn g s -> ∏ x in s.image g, f x = ∏ x in s, f (g x)
· 使用定理 `finprod_mem_eq_prod_of_inter_mulSupport_eq`：finprod_mem_eq_prod_of_inter
_mulSupport_eq (f : α -> M) {s : Set α} {t : Finset α} (h : s inter mulSupport f
 = ↑t inter mulSupport f) : ∏ᶠ i…
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用引理 `Set.image_inter_mulSupport_eq`：image_inter_mulSupport_eq : g '' s inter 
mulSupport f = g '' (s inter mulSupport (f ∘ g))
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `finprod_mem_eq_one_of_infinite`：finprod_mem_eq_one_of_infinite {f : α ->
 M} {s : Set α} (hs : (s inter mulSupport f).Infinite) : ∏ᶠ i in s, f i = 1
· 使用定理 `Set.infinite_image_iff`：infinite_image_iff {s : Set α} {f : α -> β} (hi 
: InjOn f s) : (f '' s).Infinite ↔ s.Infinite
-/
theorem finprod_mem_image' {s : Set β} {g : β → α} (hg : (s ∩ mulSupport (f ∘ g)).InjOn g) :
    ∏ᶠ i ∈ g '' s, f i = ∏ᶠ j ∈ s, f (g j) := by
  classical
    by_cases hs : (s ∩ mulSupport (f ∘ g)).Finite
    · have hg : ∀ x ∈ hs.toFinset, ∀ y ∈ hs.toFinset, g x = g y → x = y := by
        simpa only [hs.mem_toFinset]
      have := finprod_mem_eq_prod (comp f g) hs
      unfold Function.comp at this
      rw [this, ← Finset.prod_image hg]
      refine finprod_mem_eq_prod_of_inter_mulSupport_eq f ?_
      rw [Finset.coe_image, hs.coe_toFinset, ← image_inter_mulSupport_eq, inter_assoc, inter_self]
    · unfold Function.comp at hs
      rw [finprod_mem_eq_one_of_infinite hs, finprod_mem_eq_one_of_infinite]
      rwa [image_inter_mulSupport_eq, infinite_image_iff hg]

/-- The product of `f y` over `y ∈ g '' s` equals the product of `f (g i)` over `s` provided that
`g` is injective on `s`. -/
@[to_additive
      /-- The sum of `f y` over `y ∈ g '' s` equals the sum of `f (g i)` over `s` provided that
      `g` is injective on `s`. -/]
/-
**finprod_mem_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_image {s : Set β} {g : β -> α} (hg : s.InjOn g) : ∏ᶠ i in g ''
 s, f i = ∏ᶠ j in s, f (g j)
参数：hg : s.InjOn g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_image'`：finprod_mem_image' {s : Set β} {g : β -> α} (hg : (s
 inter mulSupport (f ∘ g)).InjOn g) : ∏ᶠ i in g '' s, f i = ∏ᶠ j in s, f (g j)
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem finprod_mem_image {s : Set β} {g : β → α} (hg : s.InjOn g) :
    ∏ᶠ i ∈ g '' s, f i = ∏ᶠ j ∈ s, f (g j) :=
  finprod_mem_image' <| hg.mono inter_subset_left

/-- The product of `f y` over `y ∈ Set.range g` equals the product of `f (g i)` over all `i`
provided that `g` is injective on `mulSupport (f ∘ g)`. -/
@[to_additive
      /-- The sum of `f y` over `y ∈ Set.range g` equals the sum of `f (g i)` over all `i`
      provided that `g` is injective on `support (f ∘ g)`. -/]
/-
**finprod_mem_range'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_range' {g : β -> α} (hg : (mulSupport (f ∘ g)).InjOn g) : ∏ᶠ i
 in range g, f i = ∏ᶠ j, f (g j)
参数：hg : (mulSupport (f ∘ g)).InjOn g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `finprod_mem_image'`：finprod_mem_image' {s : Set β} {g : β -> α} (hg : (s
 inter mulSupport (f ∘ g)).InjOn g) : ∏ᶠ i in g '' s, f i = ∏ᶠ j in s, f (g j)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `finprod_mem_univ`：finprod_mem_univ (f : α -> M) : ∏ᶠ i in @Set.univ α, f
 i = ∏ᶠ i : α, f i
-/
theorem finprod_mem_range' {g : β → α} (hg : (mulSupport (f ∘ g)).InjOn g) :
    ∏ᶠ i ∈ range g, f i = ∏ᶠ j, f (g j) := by
  rw [← image_univ, finprod_mem_image', finprod_mem_univ]
  rwa [univ_inter]

/-- The product of `f y` over `y ∈ Set.range g` equals the product of `f (g i)` over all `i`
provided that `g` is injective. -/
@[to_additive
      /-- The sum of `f y` over `y ∈ Set.range g` equals the sum of `f (g i)` over all `i`
      provided that `g` is injective. -/]
/-
**finprod_mem_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_range {g : β -> α} (hg : Injective g) : ∏ᶠ i in range g, f i =
 ∏ᶠ j, f (g j)
参数：hg : Injective g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_range'`：finprod_mem_range' {g : β -> α} (hg : (mulSupport (f
 ∘ g)).InjOn g) : ∏ᶠ i in range g, f i = ∏ᶠ j, f (g j)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem finprod_mem_range {g : β → α} (hg : Injective g) : ∏ᶠ i ∈ range g, f i = ∏ᶠ j, f (g j) :=
  finprod_mem_range' hg.injOn

/-- See also `Finset.prod_bij`. -/
@[to_additive /-- See also `Finset.sum_bij`. -/]
/-
**finprod_mem_eq_of_bijOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_eq_of_bijOn {s : Set α} {t : Set β} {f : α -> M} {g : β -> M} 
(e : α -> β) (he₀ : s.BijOn e t) (he₁ : forall x in s, f x = g (e x)) : ∏ᶠ i in 
s, f i = ∏ᶠ j in t, g j
参数：e : α -> β；he₀ : s.BijOn e t；he₁ : forall x in s, f x = g (e x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用定理 `finprod_mem_image`：finprod_mem_image {s : Set β} {g : β -> α} (hg : s.In
jOn g) : ∏ᶠ i in g '' s, f i = ∏ᶠ j in s, f (g j)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `finprod_mem_congr`：finprod_mem_congr (h₀ : s = t) (h₁ : forall x in t, f
 x = g x) : ∏ᶠ i in s, f i = ∏ᶠ i in t, g i

--- 原说明 ---
See also `Finset.prod_bij`.
-/
theorem finprod_mem_eq_of_bijOn {s : Set α} {t : Set β} {f : α → M} {g : β → M} (e : α → β)
    (he₀ : s.BijOn e t) (he₁ : ∀ x ∈ s, f x = g (e x)) : ∏ᶠ i ∈ s, f i = ∏ᶠ j ∈ t, g j := by
  rw [← Set.BijOn.image_eq he₀, finprod_mem_image he₀.2.1]
  exact finprod_mem_congr rfl he₁

/-- See `finprod_comp`, `Fintype.prod_bijective` and `Finset.prod_bij`. -/
@[to_additive /-- See `finsum_comp`, `Fintype.sum_bijective` and `Finset.sum_bij`. -/]
/-
**finprod_eq_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_eq_of_bijective {f : α -> M} {g : β -> M} (e : α -> β) (he₀ : Bije
ctive e) (he₁ : forall x, f x = g (e x)) : ∏ᶠ i, f i = ∏ᶠ j, g j
参数：e : α -> β；he₀ : Bijective e；he₁ : forall x, f x = g (e x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_mem_univ`：finprod_mem_univ (f : α -> M) : ∏ᶠ i in @Set.univ α, f
 i = ∏ᶠ i : α, f i
· 使用定理 `finprod_mem_eq_of_bijOn`：finprod_mem_eq_of_bijOn {s : Set α} {t : Set β}
 {f : α -> M} {g : β -> M} (e : α -> β) (he₀ : s.BijOn e t) (he₁ : forall x in s
, f x = g (e …
· 使用定理 `Function.Bijective.bijOn_univ`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β}, Function.Bijective f → Set.BijOn f Set.univ Set.univ

--- 原说明 ---
See `finprod_comp`, `Fintype.prod_bijective` and `Finset.prod_bij`.
-/
theorem finprod_eq_of_bijective {f : α → M} {g : β → M} (e : α → β) (he₀ : Bijective e)
    (he₁ : ∀ x, f x = g (e x)) : ∏ᶠ i, f i = ∏ᶠ j, g j := by
  rw [← finprod_mem_univ f, ← finprod_mem_univ g]
  exact finprod_mem_eq_of_bijOn _ he₀.bijOn_univ fun x _ => he₁ x

/-- See also `finprod_eq_of_bijective`, `Fintype.prod_bijective` and `Finset.prod_bij`. -/
@[to_additive
/-- See also `finsum_eq_of_bijective`, `Fintype.sum_bijective` and `Finset.sum_bij`. -/]
/-
**finprod_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_comp {g : β -> M} (e : α -> β) (he₀ : Function.Bijective e) : (∏ᶠ 
i, g (e i)) = ∏ᶠ j, g j
参数：e : α -> β；he₀ : Function.Bijective e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_eq_of_bijective`：finprod_eq_of_bijective {f : α -> M} {g : β -> 
M} (e : α -> β) (he₀ : Bijective e) (he₁ : forall x, f x = g (e x)) : ∏ᶠ i, f i 
= ∏ᶠ j, g j
-/
theorem finprod_comp {g : β → M} (e : α → β) (he₀ : Function.Bijective e) :
    (∏ᶠ i, g (e i)) = ∏ᶠ j, g j :=
  finprod_eq_of_bijective e he₀ fun _ => rfl

@[to_additive]
/-
**finprod_comp_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_comp_equiv (e : α ≃ β) {f : β -> M} : (∏ᶠ i, f (e i)) = ∏ᶠ i', f i
'
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_comp`：finprod_comp {g : β -> M} (e : α -> β) (he₀ : Function.Bij
ective e) : (∏ᶠ i, g (e i)) = ∏ᶠ j, g j
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
theorem finprod_comp_equiv (e : α ≃ β) {f : β → M} : (∏ᶠ i, f (e i)) = ∏ᶠ i', f i' :=
  finprod_comp e e.bijective

@[to_additive]
/-
**finprod_set_coe_eq_finprod_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_set_coe_eq_finprod_mem (s : Set α) : ∏ᶠ j : s, f j = ∏ᶠ i in s, f 
i
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_mem_range`：finprod_mem_range {g : β -> α} (hg : Injective g) : ∏
ᶠ i in range g, f i = ∏ᶠ j, f (g j)
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem finprod_set_coe_eq_finprod_mem (s : Set α) : ∏ᶠ j : s, f j = ∏ᶠ i ∈ s, f i := by
  rw [← finprod_mem_range, Subtype.range_coe]
  exact Subtype.coe_injective

@[to_additive]
/-
**finprod_subtype_eq_finprod_cond** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_subtype_eq_finprod_cond (p : α -> Prop) : ∏ᶠ j : Subtype p, f j = 
∏ᶠ (i) (_ : p i), f i
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_set_coe_eq_finprod_mem`：finprod_set_coe_eq_finprod_mem (s : Set 
α) : ∏ᶠ j : s, f j = ∏ᶠ i in s, f i
-/
theorem finprod_subtype_eq_finprod_cond (p : α → Prop) :
    ∏ᶠ j : Subtype p, f j = ∏ᶠ (i) (_ : p i), f i :=
  finprod_set_coe_eq_finprod_mem { i | p i }

@[to_additive]
/-
**finprod_mem_inter_mul_sdiff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_inter_mul_sdiff' (t : Set α) (h : (s inter mulSupport f).Finit
e) : ((∏ᶠ i in s inter t, f i) * ∏ᶠ i in s \ t, f i) = ∏ᶠ i in s, f i
参数：t : Set α；h : (s inter mulSupport f).Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_mem_union'`：finprod_mem_union' (hst : Disjoint s t) (hs : (s int
er mulSupport f).Finite) (ht : (t inter mulSupport f).Finite) : ∏ᶠ i in s union 
t, f i =…
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.inter_union_sdiff`：inter_union_sdiff (s t : Set α) : s inter t union
 s \ t = s
-/
theorem finprod_mem_inter_mul_sdiff' (t : Set α) (h : (s ∩ mulSupport f).Finite) :
    ((∏ᶠ i ∈ s ∩ t, f i) * ∏ᶠ i ∈ s \ t, f i) = ∏ᶠ i ∈ s, f i := by
  rw [← finprod_mem_union', inter_union_sdiff]
  · rw [disjoint_iff_inf_le]
    exact fun x hx => hx.2.2 hx.1.2
  exacts [h.subset fun x hx => ⟨hx.1.1, hx.2⟩, h.subset fun x hx => ⟨hx.1.1, hx.2⟩]

@[deprecated (since := "2026-06-03")]
alias finprod_mem_inter_mul_diff' := finprod_mem_inter_mul_sdiff'

@[to_additive]
/-
**finprod_mem_inter_mul_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_inter_mul_sdiff (t : Set α) (h : s.Finite) : ((∏ᶠ i in s inter
 t, f i) * ∏ᶠ i in s \ t, f i) = ∏ᶠ i in s, f i
参数：t : Set α；h : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_inter_mul_sdiff'`：finprod_mem_inter_mul_sdiff' (t : Set α) (
h : (s inter mulSupport f).Finite) : ((∏ᶠ i in s inter t, f i) * ∏ᶠ i in s \ t, 
f i) = ∏ᶠ i in s, …
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
-/
theorem finprod_mem_inter_mul_sdiff (t : Set α) (h : s.Finite) :
    ((∏ᶠ i ∈ s ∩ t, f i) * ∏ᶠ i ∈ s \ t, f i) = ∏ᶠ i ∈ s, f i :=
  finprod_mem_inter_mul_sdiff' _ <| h.inter_of_left _

@[deprecated (since := "2026-06-03")]
alias finprod_mem_inter_mul_diff := finprod_mem_inter_mul_sdiff

/-- A more general version of `finprod_mem_mul_diff` that requires `t ∩ mulSupport f` rather than
`t` to be finite. -/
@[to_additive
      /-- A more general version of `finsum_mem_add_diff` that requires `t ∩ support f` rather
      than `t` to be finite. -/]
/-
**finprod_mem_mul_sdiff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_mul_sdiff' (hst : s subseteq t) (ht : (t inter mulSupport f).F
inite) : ((∏ᶠ i in s, f i) * ∏ᶠ i in t \ s, f i) = ∏ᶠ i in t, f i
参数：hst : s subseteq t；ht : (t inter mulSupport f).Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_mem_inter_mul_sdiff'`：finprod_mem_inter_mul_sdiff' (t : Set α) (
h : (s inter mulSupport f).Finite) : ((∏ᶠ i in s inter t, f i) * ∏ᶠ i in s \ t, 
f i) = ∏ᶠ i in s, …
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
-/
theorem finprod_mem_mul_sdiff' (hst : s ⊆ t) (ht : (t ∩ mulSupport f).Finite) :
    ((∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t \ s, f i) = ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mul_sdiff' _ ht, inter_eq_self_of_subset_right hst]

@[deprecated (since := "2026-06-03")] alias finprod_mem_mul_diff' := finprod_mem_mul_sdiff'

/-- Given a finite set `t` and a subset `s` of `t`, the product of `f i` over `i ∈ s`
times the product of `f i` over `t \ s` equals the product of `f i` over `i ∈ t`. -/
@[to_additive
      /-- Given a finite set `t` and a subset `s` of `t`, the sum of `f i` over `i ∈ s` plus
      the sum of `f i` over `t \ s` equals the sum of `f i` over `i ∈ t`. -/]
/-
**finprod_mem_mul_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_mul_sdiff (hst : s subseteq t) (ht : t.Finite) : ((∏ᶠ i in s, 
f i) * ∏ᶠ i in t \ s, f i) = ∏ᶠ i in t, f i
参数：hst : s subseteq t；ht : t.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_mul_sdiff'`：finprod_mem_mul_sdiff' (hst : s subseteq t) (ht 
: (t inter mulSupport f).Finite) : ((∏ᶠ i in s, f i) * ∏ᶠ i in t \ s, f i) = ∏ᶠ 
i in t, f i
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
-/
theorem finprod_mem_mul_sdiff (hst : s ⊆ t) (ht : t.Finite) :
    ((∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t \ s, f i) = ∏ᶠ i ∈ t, f i :=
  finprod_mem_mul_sdiff' hst (ht.inter_of_left _)

@[deprecated (since := "2026-06-03")] alias finprod_mem_mul_diff := finprod_mem_mul_sdiff

/-- Given a family of pairwise disjoint finite sets `t i` indexed by a finite type, the product of
`f a` over the union `⋃ i, t i` is equal to the product over all indexes `i` of the products of
`f a` over `a ∈ t i`. -/
@[to_additive
      /-- Given a family of pairwise disjoint finite sets `t i` indexed by a finite type, the
      sum of `f a` over the union `⋃ i, t i` is equal to the sum over all indexes `i` of the
      sums of `f a` over `a ∈ t i`. -/]
/-
**finprod_mem_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_iUnion [Finite ι] {t : ι -> Set α} (h : Pairwise (Disjoint on 
t)) (ht : forall i, (t i).Finite) : ∏ᶠ a in ⋃ i : ι, t i, f a = ∏ᶠ i, ∏ᶠ a in t 
i, f a
参数：h : Pairwise (Disjoint on t)；ht : forall i, (t i).Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_univ`：biUnion_univ (s : α -> Set β) : ⋃ x in @univ α, s x = 
⋃ x, s x
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
· 使用定理 `finprod_mem_coe_finset`：finprod_mem_coe_finset (f : α -> M) (s : Finset 
α) : (∏ᶠ i in (s : Set α), f i) = ∏ i in s, f i
· 使用定理 `Finset.prod_biUnion`：prod_biUnion [DecidableEq ι] {s : Finset κ} {t : κ 
-> Finset ι} (hs : Set.PairwiseDisjoint (↑s) t) : ∏ x in s.biUnion t, f x = ∏ x 
in s, ∏ i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.disjoint_coe`：disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s 
t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finprod_eq_prod_of_fintype`：finprod_eq_prod_of_fintype [Fintype α] (f : 
α -> M) : ∏ᶠ i : α, f i = ∏ i, f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finprod_mem_iUnion [Finite ι] {t : ι → Set α} (h : Pairwise (Disjoint on t))
    (ht : ∀ i, (t i).Finite) : ∏ᶠ a ∈ ⋃ i : ι, t i, f a = ∏ᶠ i, ∏ᶠ a ∈ t i, f a := by
  cases nonempty_fintype ι
  lift t to ι → Finset α using ht
  classical
    rw [← biUnion_univ, ← Finset.coe_univ, ← Finset.coe_biUnion, finprod_mem_coe_finset,
      Finset.prod_biUnion]
    · simp only [finprod_mem_coe_finset, finprod_eq_prod_of_fintype]
    · exact fun x _ y _ hxy => Finset.disjoint_coe.1 (h hxy)

/-- Given a family of sets `t : ι → Set α`, a finite set `I` in the index type such that all sets
`t i`, `i ∈ I`, are finite, if all `t i`, `i ∈ I`, are pairwise disjoint, then the product of `f a`
over `a ∈ ⋃ i ∈ I, t i` is equal to the product over `i ∈ I` of the products of `f a` over
`a ∈ t i`. -/
@[to_additive
      /-- Given a family of sets `t : ι → Set α`, a finite set `I` in the index type such that
      all sets `t i`, `i ∈ I`, are finite, if all `t i`, `i ∈ I`, are pairwise disjoint, then the
      sum of `f a` over `a ∈ ⋃ i ∈ I, t i` is equal to the sum over `i ∈ I` of the sums of `f a`
      over `a ∈ t i`. -/]
/-
**finprod_mem_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_biUnion {I : Set ι} {t : ι -> Set α} (h : I.PairwiseDisjoint t
) (hI : I.Finite) (ht : forall i in I, (t i).Finite) : ∏ᶠ a in ⋃ x in I, t x, f 
a = ∏ᶠ i in I, ∏ᶠ j in t i, f j
参数：h : I.PairwiseDisjoint t；hI : I.Finite；ht : forall i in I, (t i).Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `finprod_mem_iUnion`：finprod_mem_iUnion [Finite ι] {t : ι -> Set α} (h : 
Pairwise (Disjoint on t)) (ht : forall i, (t i).Finite) : ∏ᶠ a in ⋃ i : ι, t i, 
f a = ∏ᶠ…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_set_coe_eq_finprod_mem`：finprod_set_coe_eq_finprod_mem (s : Set 
α) : ∏ᶠ j : s, f j = ∏ᶠ i in s, f i
-/
theorem finprod_mem_biUnion {I : Set ι} {t : ι → Set α} (h : I.PairwiseDisjoint t) (hI : I.Finite)
    (ht : ∀ i ∈ I, (t i).Finite) : ∏ᶠ a ∈ ⋃ x ∈ I, t x, f a = ∏ᶠ i ∈ I, ∏ᶠ j ∈ t i, f j := by
  have := hI.fintype
  rw [biUnion_eq_iUnion, finprod_mem_iUnion, ← finprod_set_coe_eq_finprod_mem]
  exacts [fun x y hxy => h x.2 y.2 (Subtype.coe_injective.ne hxy), fun b => ht b b.2]

/-- If `t` is a finite set of pairwise disjoint finite sets, then the product of `f a`
over `a ∈ ⋃₀ t` is the product over `s ∈ t` of the products of `f a` over `a ∈ s`. -/
@[to_additive
      /-- If `t` is a finite set of pairwise disjoint finite sets, then the sum of `f a` over
      `a ∈ ⋃₀ t` is the sum over `s ∈ t` of the sums of `f a` over `a ∈ s`. -/]
/-
**finprod_mem_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_sUnion {t : Set (Set α)} (h : t.PairwiseDisjoint id) (ht₀ : t.
Finite) (ht₁ : forall x in t, Set.Finite x) : ∏ᶠ a in ⋃₀ t, f a = ∏ᶠ s in t, ∏ᶠ 
a in s, f a
参数：Set α；h : t.PairwiseDisjoint id；ht₀ : t.Finite；ht₁ : forall x in t, Set.Finit
e x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `finprod_mem_biUnion`：finprod_mem_biUnion {I : Set ι} {t : ι -> Set α} (h
 : I.PairwiseDisjoint t) (hI : I.Finite) (ht : forall i in I, (t i).Finite) : ∏ᶠ
 a in ⋃ x…
-/
theorem finprod_mem_sUnion {t : Set (Set α)} (h : t.PairwiseDisjoint id) (ht₀ : t.Finite)
    (ht₁ : ∀ x ∈ t, Set.Finite x) : ∏ᶠ a ∈ ⋃₀ t, f a = ∏ᶠ s ∈ t, ∏ᶠ a ∈ s, f a := by
  rw [Set.sUnion_eq_biUnion]
  exact finprod_mem_biUnion h ht₀ ht₁

@[to_additive]
/-
**finprod_option** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finprod_option {f : Option α -> M} (hf : HasFiniteMulSupport (f ∘ some)) :
 ∏ᶠ o, f o = f none * ∏ᶠ a, f (some a)
参数：hf : HasFiniteMulSupport (f ∘ some)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `finprod_congr_Prop`：finprod_congr_Prop {p q : Prop} {f : p -> M} {g : q 
-> M} (hpq : p = q) (hfg : forall h : q, f (hpq.mpr h) = g h) : finprod f = finp
rod g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_none_range_some`：insert_none_range_some (α : Type*) : insert 
none (range (some : α -> Option α)) = univ
· 使用定理 `finprod_true`：finprod_true (f : True -> M) : ∏ᶠ i, f i = f trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `finprod_mem_range`：finprod_mem_range {g : β -> α} (hg : Injective g) : ∏
ᶠ i in range g, f i = ∏ᶠ j, f (g j)
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
· 使用定理 `finprod_mem_insert'`：finprod_mem_insert' (f : α -> M) (h : a ∉ s) (hs : 
(s inter mulSupport f).Finite) : ∏ᶠ i in insert a s, f i = f a * ∏ᶠ i in s, f i
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma finprod_option {f : Option α → M} (hf : HasFiniteMulSupport (f ∘ some)) :
    ∏ᶠ o, f o = f none * ∏ᶠ a, f (some a) := by
  replace hf : (mulSupport f).Finite := by simpa [finite_option]
  convert!
    finprod_mem_insert' f (show none ∉ Set.range Option.some by simp) (hf.subset inter_subset_right)
  · simp
  · rw [finprod_mem_range]
    exact Option.some_injective _

@[to_additive]
/-
**finprod_mem_powerset_insert** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finprod_mem_powerset_insert {f : Set α -> M} {s : Set α} {a : α} (hs : s.F
inite) (has : a ∉ s) : ∏ᶠ t in 𝒫 insert a s, f t = (∏ᶠ t in 𝒫 s, f t) * ∏ᶠ t in 
𝒫 s, f (insert a t)
参数：hs : s.Finite；has : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.powerset_insert`：powerset_insert (s : Set α) (a : α) : 𝒫 insert a s 
= 𝒫 s union insert a '' 𝒫 s
· 使用定理 `finprod_mem_union`：finprod_mem_union (hst : Disjoint s t) (hs : s.Finite
) (ht : t.Finite) : ∏ᶠ i in s union t, f i = (∏ᶠ i in s, f i) * ∏ᶠ i in t, f i
· 使用定理 `Set.disjoint_powerset_insert`：disjoint_powerset_insert {s : Set α} {a : 
α} (h : a ∉ s) : Disjoint (𝒫 s) (insert a '' 𝒫 s)
· 使用定理 `Set.Finite.powerset`：∀ {α : Type u} {s : Set α}, s.Finite → (𝒫 s).Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `finprod_mem_image`：finprod_mem_image {s : Set β} {g : β -> α} (hg : s.In
jOn g) : ∏ᶠ i in g '' s, f i = ∏ᶠ j in s, f (g j)
· 使用定理 `Set.powerset_insert_injOn`：powerset_insert_injOn {s : Set α} {a : α} (h 
: a ∉ s) : Set.InjOn (insert a) (𝒫 s)
-/
lemma finprod_mem_powerset_insert {f : Set α → M} {s : Set α} {a : α} (hs : s.Finite)
    (has : a ∉ s) : ∏ᶠ t ∈ 𝒫 insert a s, f t = (∏ᶠ t ∈ 𝒫 s, f t) * ∏ᶠ t ∈ 𝒫 s, f (insert a t) := by
  rw [Set.powerset_insert,
    finprod_mem_union (disjoint_powerset_insert has) hs.powerset (hs.powerset.image (insert a)),
    finprod_mem_image (powerset_insert_injOn has)]

@[to_additive]
/-
**finprod_mem_powerset_sdiff_elem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finprod_mem_powerset_sdiff_elem {f : Set α -> M} {s : Set α} {a : α} (hs :
 s.Finite) (has : a in s) : ∏ᶠ t in 𝒫 s, f t = (∏ᶠ t in 𝒫 (s \ {a}), f t) * ∏ᶠ t
 in 𝒫 (s \ {a}), f (insert a t)
参数：hs : s.Finite；has : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.insert_sdiff_self_of_mem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ 
s → insert a (s \ {a}) = s
· 使用引理 `finprod_mem_powerset_insert`：finprod_mem_powerset_insert {f : Set α -> M
} {s : Set α} {a : α} (hs : s.Finite) (has : a ∉ s) : ∏ᶠ t in 𝒫 insert a s, f t 
= (∏ᶠ t in 𝒫 s, f…
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.notMem_sdiff_of_mem`：notMem_sdiff_of_mem {s t : Set α} {x : α} (hx :
 x in t) : x ∉ s \ t
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
lemma finprod_mem_powerset_sdiff_elem {f : Set α → M} {s : Set α} {a : α} (hs : s.Finite)
    (has : a ∈ s) : ∏ᶠ t ∈ 𝒫 s, f t = (∏ᶠ t ∈ 𝒫 (s \ {a}), f t)
    * ∏ᶠ t ∈ 𝒫 (s \ {a}), f (insert a t) := by
  nth_rw 1 2 [← Set.insert_sdiff_self_of_mem has] -- second appearance hidden by notation
  exact finprod_mem_powerset_insert (hs.subset Set.sdiff_subset)
    (notMem_sdiff_of_mem (Set.mem_singleton a))

@[deprecated (since := "2026-06-03")]
alias finprod_mem_powerset_diff_elem := finprod_mem_powerset_sdiff_elem

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**mul_finprod_cond_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_finprod_cond_ne (a : α) (hf : HasFiniteMulSupport f) : (f a * ∏ᶠ (i) (
_ : i != a), f i) = ∏ᶠ i, f i
参数：a : α；hf : HasFiniteMulSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_prod`：finprod_eq_prod (f : α -> M) (hf : HasFiniteMulSupport 
f) : ∏ᶠ i : α, f i = ∏ i in hf.toFinset, f i
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用引理 `Function.mem_mulSupport`：mem_mulSupport : x in mulSupport f ↔ f x != 1
· 使用定理 `finprod_cond_eq_prod_of_cond_iff`：finprod_cond_eq_prod_of_cond_iff (f : 
α -> M) {p : α -> Prop} {t : Finset α} (h : forall {x}, f x != 1 -> (p x ↔ x in 
t)) : (∏ᶠ (i) (_ : p i…
· 使用定理 `Finset.sdiff_singleton_eq_erase`：sdiff_singleton_eq_erase (a : α) (s : F
inset α) : s \ {a} = s.erase a
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.prod_erase`：prod_erase [DecidableEq ι] (s : Finset ι) {f : ι -> M
} {a : ι} (h : f a = 1) : ∏ x in s.erase a, f x = ∏ x in s, f x
-/
theorem mul_finprod_cond_ne (a : α) (hf : HasFiniteMulSupport f) :
    (f a * ∏ᶠ (i) (_ : i ≠ a), f i) = ∏ᶠ i, f i := by
  classical
    rw [finprod_eq_prod _ hf]
    have h : ∀ x : α, f x ≠ 1 → (x ≠ a ↔ x ∈ hf.toFinset \ {a}) := by
      intro x hx
      rw [Finset.mem_sdiff, Finset.mem_singleton, Finite.mem_toFinset, mem_mulSupport]
      grind
    rw [finprod_cond_eq_prod_of_cond_iff f (fun hx => h _ hx), Finset.sdiff_singleton_eq_erase]
    by_cases ha : a ∈ mulSupport f
    · apply Finset.mul_prod_erase _ _ ((Finite.mem_toFinset _).mpr ha)
    · rw [mem_mulSupport, not_not] at ha
      rw [ha, one_mul]
      apply Finset.prod_erase _ ha

/-- If `s : Set α` and `t : Set β` are finite sets, then taking the product over `s` commutes with
taking the product over `t`. -/
@[to_additive
      /-- If `s : Set α` and `t : Set β` are finite sets, then summing over `s` commutes with
      summing over `t`. -/]
/-
**finprod_mem_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_comm {s : Set α} {t : Set β} (f : α -> β -> M) (hs : s.Finite)
 (ht : t.Finite) : (∏ᶠ i in s, ∏ᶠ j in t, f i j) = ∏ᶠ j in t, ∏ᶠ i in s, f i j
参数：f : α -> β -> M；hs : s.Finite；ht : t.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finprod_congr_Prop`：finprod_congr_Prop {p q : Prop} {f : p -> M} {g : q 
-> M} (hpq : p = q) (hfg : forall h : q, f (hpq.mpr h) = g h) : finprod f = finp
rod g
· 使用定理 `finprod_mem_coe_finset`：finprod_mem_coe_finset (f : α -> M) (s : Finset 
α) : (∏ᶠ i in (s : Set α), f i) = ∏ i in s, f i
· 使用定理 `Finset.prod_comm`：prod_comm {s : Finset γ} {t : Finset α} {f : γ -> α ->
 β} : (∏ x in s, ∏ y in t, f x y) = ∏ y in t, ∏ x in s, f x y
-/
theorem finprod_mem_comm {s : Set α} {t : Set β} (f : α → β → M) (hs : s.Finite) (ht : t.Finite) :
    (∏ᶠ i ∈ s, ∏ᶠ j ∈ t, f i j) = ∏ᶠ j ∈ t, ∏ᶠ i ∈ s, f i j := by
  lift s to Finset α using hs; lift t to Finset β using ht
  simp only [finprod_mem_coe_finset]
  exact Finset.prod_comm

/-- To prove a property of a finite product, it suffices to prove that the property is
multiplicative and holds on factors. -/
@[to_additive
      /-- To prove a property of a finite sum, it suffices to prove that the property is
      additive and holds on summands. -/]
/-
**finprod_mem_induction** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_induction (p : M -> Prop) (hp₀ : p 1) (hp₁ : forall x y, p x -
> p y -> p (x * y)) (hp₂ : forall x in s, p <| f x) : p (∏ᶠ i in s, f i)
参数：p : M -> Prop；hp₀ : p 1；hp₁ : forall x y, p x -> p y -> p (x * y)；hp₂ : foral
l x in s, p <| f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_induction`：finprod_induction {f : α -> M} (p : M -> Prop) (hp₀ :
 p 1) (hp₁ : forall x y, p x -> p y -> p (x * y)) (hp₂ : forall i, p (f i)) : p 
(∏ᶠ i, …
-/
theorem finprod_mem_induction (p : M → Prop) (hp₀ : p 1) (hp₁ : ∀ x y, p x → p y → p (x * y))
    (hp₂ : ∀ x ∈ s, p <| f x) : p (∏ᶠ i ∈ s, f i) :=
  finprod_induction _ hp₀ hp₁ fun x => finprod_induction _ hp₀ hp₁ <| hp₂ x
/-
**finprod_cond_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_cond_nonneg {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrder
edRing R] {p : α -> Prop} {f : α -> R} (hf : forall x, p x -> 0 <= f x) : 0 <= ∏
ᶠ (x) (_ : p x), f x
参数：hf : forall x, p x -> 0 <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_nonneg`：finprod_nonneg {R : Type*} [CommMonoidWithZero R] [Preor
der R] [ZeroLEOneClass R] [PosMulMono R] {f : α -> R} (hf : forall x, 0 <= f x) 
: 0 …
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem finprod_cond_nonneg {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    {p : α → Prop} {f : α → R}
    (hf : ∀ x, p x → 0 ≤ f x) : 0 ≤ ∏ᶠ (x) (_ : p x), f x :=
  finprod_nonneg fun x => finprod_nonneg <| hf x

@[to_additive]
/-
**single_le_finprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：single_le_finprod {M : Type*} [CommMonoid M] [Preorder M] [IsOrderedMonoid
 M] (i : α) {f : α -> M} (hf : HasFiniteMulSupport f) (h : forall j, 1 <= f j) :
 f i <= ∏ᶠ j, f j
参数：i : α；hf : HasFiniteMulSupport f；h : forall j, 1 <= f j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.single_le_prod'`：single_le_prod' [MulLeftMono N] (hf : forall i i
n s, 1 <= f i) {a} (h : a in s) : f a <= ∏ x in s, f x
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_eq_prod_of_mulSupport_toFinset_subset`：finprod_eq_prod_of_mulSup
port_toFinset_subset (f : α -> M) (hf : HasFiniteMulSupport f) {s : Finset α} (h
 : hf.toFinset subseteq s) : ∏ᶠ i, …
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
-/
theorem single_le_finprod {M : Type*} [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
    (i : α) {f : α → M}
    (hf : HasFiniteMulSupport f) (h : ∀ j, 1 ≤ f j) : f i ≤ ∏ᶠ j, f j := by
  classical calc
      f i ≤ ∏ j ∈ insert i hf.toFinset, f j :=
        Finset.single_le_prod' (fun j _ => h j) (Finset.mem_insert_self _ _)
      _ = ∏ᶠ j, f j :=
        (finprod_eq_prod_of_mulSupport_toFinset_subset _ hf (Finset.subset_insert _ _)).symm
/-
**finprod_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_eq_zero {M₀ : Type*} [CommMonoidWithZero M₀] (f : α -> M₀) (x : α)
 (hx : f x = 0) (hf : HasFiniteMulSupport f) : ∏ᶠ x, f x = 0
参数：f : α -> M₀；x : α；hx : f x = 0；hf : HasFiniteMulSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_prod`：finprod_eq_prod (f : α -> M) (hf : HasFiniteMulSupport 
f) : ∏ᶠ i : α, f i = ∏ i in hf.toFinset, f i
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem finprod_eq_zero {M₀ : Type*} [CommMonoidWithZero M₀] (f : α → M₀) (x : α) (hx : f x = 0)
    (hf : HasFiniteMulSupport f) : ∏ᶠ x, f x = 0 := by
  nontriviality
  rw [finprod_eq_prod f hf]
  refine Finset.prod_eq_zero (hf.mem_toFinset.2 ?_) hx
  simp [hx]

@[to_additive]
/-
**finprod_prod_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_prod_comm (s : Finset β) (f : α -> β -> M) (h : forall b in s, Has
FiniteMulSupport fun a => f a b) : (∏ᶠ a : α, ∏ b in s, f a b) = ∏ b in s, ∏ᶠ a 
: α, f a b
参数：s : Finset β；f : α -> β -> M；h : forall b in s, HasFiniteMulSupport fun a => 
f a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用引理 `Function.mem_mulSupport`：mem_mulSupport : x in mulSupport f ↔ f x != 1
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
· 使用定理 `Finset.prod_comm`：prod_comm {s : Finset γ} {t : Finset α} {f : γ -> α ->
 β} : (∏ x in s, ∏ y in t, f x y) = ∏ y in t, ∏ x in s, f x y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem finprod_prod_comm (s : Finset β) (f : α → β → M)
    (h : ∀ b ∈ s, HasFiniteMulSupport fun a ↦ f a b) :
    (∏ᶠ a : α, ∏ b ∈ s, f a b) = ∏ b ∈ s, ∏ᶠ a : α, f a b := by
  have hU :
    (mulSupport fun a => ∏ b ∈ s, f a b) ⊆
      (s.finite_toSet.biUnion fun b hb => h b (Finset.mem_coe.1 hb)).toFinset := by
    rw [Finite.coe_toFinset]
    intro x hx
    simp only [exists_prop, mem_iUnion, Ne, mem_mulSupport, Finset.mem_coe]
    contrapose! hx
    rw [mem_mulSupport, not_not, Finset.prod_congr rfl hx, Finset.prod_const_one]
  rw [finprod_eq_prod_of_mulSupport_subset _ hU, Finset.prod_comm]
  refine Finset.prod_congr rfl fun b hb => (finprod_eq_prod_of_mulSupport_subset _ ?_).symm
  intro a ha
  simp only [Finite.coe_toFinset, mem_iUnion]
  exact ⟨b, hb, ha⟩

@[to_additive]
/-
**prod_finprod_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prod_finprod_comm (s : Finset α) (f : α -> β -> M) (h : forall a in s, Has
FiniteMulSupport (f a)) : (∏ a in s, ∏ᶠ b : β, f a b) = ∏ᶠ b : β, ∏ a in s, f a 
b
参数：s : Finset α；f : α -> β -> M；h : forall a in s, HasFiniteMulSupport (f a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_prod_comm`：finprod_prod_comm (s : Finset β) (f : α -> β -> M) (h
 : forall b in s, HasFiniteMulSupport fun a => f a b) : (∏ᶠ a : α, ∏ b in s, f a
 b) = ∏…
-/
theorem prod_finprod_comm (s : Finset α) (f : α → β → M) (h : ∀ a ∈ s, HasFiniteMulSupport (f a)) :
    (∏ a ∈ s, ∏ᶠ b : β, f a b) = ∏ᶠ b : β, ∏ a ∈ s, f a b :=
  (finprod_prod_comm s (fun b a => f a b) h).symm

@[to_additive]
/-
**finprod_prod_filter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_prod_filter [DecidableEq α] (f : β -> α) (s : Finset β) (g : β -> 
M) : ∏ᶠ x, ∏ y in s with f y = x, g y = ∏ k in s, g k
参数：f : β -> α；s : Finset β；g : β -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_finsetProd_of_mulSupport_subset`：finprod_eq_finsetProd_of_mul
Support_subset (f : α -> M) {s : Finset α} (h : mulSupport f subseteq (s : Set α
)) : ∏ᶠ i, f i = ∏ i in s, f i
· 使用定理 `Finset.exists_ne_one_of_prod_ne_one`：exists_ne_one_of_prod_ne_one (h : ∏
 x in s, f x != 1) : exists a in s, f a != 1
· 使用引理 `Function.mem_mulSupport`：mem_mulSupport : x in mulSupport f ↔ f x != 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_image'`：prod_image' [DecidableEq ι] {s : Finset κ} {g : κ ->
 ι} (h : κ -> M) (eq : forall i in s, f (g i) = ∏ j in s with g j = g i, h j) : 
∏ a in s…
-/
theorem finprod_prod_filter [DecidableEq α] (f : β → α) (s : Finset β) (g : β → M) :
    ∏ᶠ x, ∏ y ∈ s with f y = x, g y = ∏ k ∈ s, g k := by
  rw [finprod_eq_finsetProd_of_mulSupport_subset]
  · rw [Finset.prod_image']
    exact fun _ _ ↦ rfl
  · intro x hx
    rw [mem_mulSupport] at hx
    obtain ⟨a, h, -⟩ := Finset.exists_ne_one_of_prod_ne_one hx
    simp only [Finset.mem_filter, Finset.coe_image, mem_image, SetLike.mem_coe] at h ⊢
    exact ⟨a, h⟩

/--
For functions with finite support, multiplication commutes with finsums. See `mul_finsum` for a
statement assuming that `R` has no zero divisors.
-/
/-
**mul_finsum'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_finsum' {R : Type*} [NonUnitalNonAssocSemiring R] (f : α -> R) (r : R)
 (h : HasFiniteSupport f) : (r * ∑ᶠ a : α, f a) = ∑ᶠ a : α, r * f a
参数：f : α -> R；r : R；h : HasFiniteSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_finsum`：∀ {α : Type u_1} {M : Type u_5} {N : Type u_6} 
[inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] {f : α → M}   (g : M →+ N), 
Function.HasF…

--- 原说明 ---
For functions with finite support, multiplication commutes with finsums. See `mu
l_finsum` for a
statement assuming that `R` has no zero divisors.
-/
theorem mul_finsum' {R : Type*} [NonUnitalNonAssocSemiring R] (f : α → R) (r : R)
    (h : HasFiniteSupport f) : (r * ∑ᶠ a : α, f a) = ∑ᶠ a : α, r * f a :=
  (AddMonoidHom.mulLeft r).map_finsum h

/--
For finite sets, multiplication commutes with `finsum_mem`. See `mul_finsum_mem'` for a statement
assuming finiteness of support.
-/
/-
**mul_finsum_mem'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_finsum_mem' {R : Type*} [NonUnitalNonAssocSemiring R] {s : Set α} (f :
 α -> R) (r : R) (hs : s.Finite) : (r * ∑ᶠ a in s, f a) = ∑ᶠ a in s, r * f a
参数：f : α -> R；r : R；hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_finsum_mem`：∀ {α : Type u_1} {M : Type u_5} {N : Type u
_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] {s : Set α}   (f : α → M
) (g : M →+ N), s…

--- 原说明 ---
For finite sets, multiplication commutes with `finsum_mem`. See `mul_finsum_mem'
` for a statement
assuming finiteness of support.
-/
theorem mul_finsum_mem' {R : Type*} [NonUnitalNonAssocSemiring R] {s : Set α} (f : α → R) (r : R)
    (hs : s.Finite) : (r * ∑ᶠ a ∈ s, f a) = ∑ᶠ a ∈ s, r * f a :=
  (AddMonoidHom.mulLeft r).map_finsum_mem f hs

/--
For functions with finite support, multiplication commutes with finsums. See `finsum_mul` for a
statement assuming that `R` has no zero divisors.
-/
/-
**finsum_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsum_mul' {R : Type*} [NonUnitalNonAssocSemiring R] (f : α -> R) (r : R)
 (h : HasFiniteSupport f) : (∑ᶠ a : α, f a) * r = ∑ᶠ a : α, f a * r
参数：f : α -> R；r : R；h : HasFiniteSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_finsum`：∀ {α : Type u_1} {M : Type u_5} {N : Type u_6} 
[inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] {f : α → M}   (g : M →+ N), 
Function.HasF…

--- 原说明 ---
For functions with finite support, multiplication commutes with finsums. See `fi
nsum_mul` for a
statement assuming that `R` has no zero divisors.
-/
theorem finsum_mul' {R : Type*} [NonUnitalNonAssocSemiring R] (f : α → R) (r : R)
    (h : HasFiniteSupport f) : (∑ᶠ a : α, f a) * r = ∑ᶠ a : α, f a * r :=
  (AddMonoidHom.mulRight r).map_finsum h

/--
For finite sets, multiplication commutes with `finsum_mem`. See `finsum_mem_mul'` for a statement
assuming finiteness of support.
-/
/-
**finsum_mem_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsum_mem_mul' {R : Type*} [NonUnitalNonAssocSemiring R] {s : Set α} (f :
 α -> R) (r : R) (hs : s.Finite) : (∑ᶠ a in s, f a) * r = ∑ᶠ a in s, f a * r
参数：f : α -> R；r : R；hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_finsum_mem`：∀ {α : Type u_1} {M : Type u_5} {N : Type u
_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] {s : Set α}   (f : α → M
) (g : M →+ N), s…

--- 原说明 ---
For finite sets, multiplication commutes with `finsum_mem`. See `finsum_mem_mul'
` for a statement
assuming finiteness of support.
-/
theorem finsum_mem_mul' {R : Type*} [NonUnitalNonAssocSemiring R] {s : Set α} (f : α → R) (r : R)
    (hs : s.Finite) : (∑ᶠ a ∈ s, f a) * r = ∑ᶠ a ∈ s, f a * r :=
  (AddMonoidHom.mulRight r).map_finsum_mem f hs

/--
If `R` has no zero divisors, then multiplication commutes with finsums. See `mul_finsum'` for a
statement assuming finiteness of support.
-/
/-
**mul_finsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_finsum {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] (f
 : α -> R) (r : R) : (r * ∑ᶠ a : α, f a) = ∑ᶠ a : α, r * f a
参数：f : α -> R；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finsum_zero`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid M], ∑
ᶠ (x : α), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_finsum'`：mul_finsum' {R : Type*} [NonUnitalNonAssocSemiring R] (f : 
α -> R) (r : R) (h : HasFiniteSupport f) : (r * ∑ᶠ a : α, f a) = ∑ᶠ a : α, r * f
 …
· 使用定理 `finsum_def`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] (f 
: α → M) [inst_1 : Decidable (Function.HasFiniteSupport f)],   ∑ᶠ (i : α), f i =
…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `R` has no zero divisors, then multiplication commutes with finsums. See `mul
_finsum'` for a
statement assuming finiteness of support.
-/
theorem mul_finsum {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] (f : α → R)
    (r : R) :
    (r * ∑ᶠ a : α, f a) = ∑ᶠ a : α, r * f a := by
  classical
  by_cases hr : r = 0
  · simp_all
  by_cases h : f.support.Finite
  · exact mul_finsum' f r h
  simp [finsum_def, HasFiniteSupport, h, (by aesop : (r * f ·).support = f.support)]

/--
If `R` has no zero divisors, then multiplication commutes with `finsum_mem`. See `mul_finsum_mem'`
for a statement assuming finiteness of support.
-/
/-
**mul_finsum_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_finsum_mem {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R
] {s : Set α} (f : α -> R) (r : R) : (r * ∑ᶠ a in s, f a) = ∑ᶠ a in s, r * f a
参数：f : α -> R；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_finsum`：mul_finsum {R : Type*} [NonUnitalNonAssocSemiring R] [NoZero
Divisors R] (f : α -> R) (r : R) : (r * ∑ᶠ a : α, f a) = ∑ᶠ a : α, r * f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `finsum_congr_Prop`：∀ {M : Type u_2} [inst : AddCommMonoid M] {p q : Prop
} {f : p → M} {g : q → M} (hpq : p = q),   (∀ (h : q), f ⋯ = g h) → finsum f = f
insum g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `finsum_true`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : True → M), ∑
ᶠ (i : True), f i = f trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `finsum_false`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : False → M),
 ∑ᶠ (i : False), f i = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
If `R` has no zero divisors, then multiplication commutes with `finsum_mem`. See
 `mul_finsum_mem'`
for a statement assuming finiteness of support.
-/
theorem mul_finsum_mem {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] {s : Set α}
    (f : α → R) (r : R) :
    (r * ∑ᶠ a ∈ s, f a) = ∑ᶠ a ∈ s, r * f a := by
  rw [mul_finsum]
  congr
  ext a
  by_cases h : a ∈ s <;> simp_all

/--
If `R` has no zero divisors, then multiplication commutes with finsums. See `finsum_mul'` for a
statement assuming finiteness of support.
-/
/-
**finsum_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsum_mul {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] (f
 : α -> R) (r : R) : (∑ᶠ a : α, f a) * r = ∑ᶠ a : α, f a * r
参数：f : α -> R；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finsum_zero`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid M], ∑
ᶠ (x : α), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `finsum_mul'`：finsum_mul' {R : Type*} [NonUnitalNonAssocSemiring R] (f : 
α -> R) (r : R) (h : HasFiniteSupport f) : (∑ᶠ a : α, f a) * r = ∑ᶠ a : α, f a *
 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `finsum_def`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] (f 
: α → M) [inst_1 : Decidable (Function.HasFiniteSupport f)],   ∑ᶠ (i : α), f i =
…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `R` has no zero divisors, then multiplication commutes with finsums. See `fin
sum_mul'` for a
statement assuming finiteness of support.
-/
theorem finsum_mul {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] (f : α → R)
    (r : R) :
    (∑ᶠ a : α, f a) * r = ∑ᶠ a : α, f a * r := by
  classical
  by_cases hr : r = 0
  · simp_all
  by_cases h : f.support.Finite
  · exact finsum_mul' f r h
  simp [finsum_def, HasFiniteSupport, h, (by aesop : (f · * r).support = f.support)]

/--
If `R` has no zero divisors, then multiplication commutes with `finsum_mem`. See `finsum_mem_mul'`
for a statement assuming finiteness of support.
-/
/-
**finsum_mem_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsum_mem_mul {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R
] {s : Set α} (f : α -> R) (r : R) : (∑ᶠ a in s, f a) * r = ∑ᶠ a in s, f a * r
参数：f : α -> R；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_mul`：finsum_mul {R : Type*} [NonUnitalNonAssocSemiring R] [NoZero
Divisors R] (f : α -> R) (r : R) : (∑ᶠ a : α, f a) * r = ∑ᶠ a : α, f a * r
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `finsum_congr_Prop`：∀ {M : Type u_2} [inst : AddCommMonoid M] {p q : Prop
} {f : p → M} {g : q → M} (hpq : p = q),   (∀ (h : q), f ⋯ = g h) → finsum f = f
insum g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `finsum_true`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : True → M), ∑
ᶠ (i : True), f i = f trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `finsum_false`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : False → M),
 ∑ᶠ (i : False), f i = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0

--- 原说明 ---
If `R` has no zero divisors, then multiplication commutes with `finsum_mem`. See
 `finsum_mem_mul'`
for a statement assuming finiteness of support.
-/
theorem finsum_mem_mul {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] {s : Set α}
    (f : α → R) (r : R) :
    (∑ᶠ a ∈ s, f a) * r = ∑ᶠ a ∈ s, f a * r := by
  rw [finsum_mul]
  congr
  ext a
  by_cases h : a ∈ s <;> simp_all

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**finprod_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finprod_apply {α ι : Type*} {f : ι -> α -> N} (hf : HasFiniteMulSupport f)
 (a : α) : (∏ᶠ i, f i) a = ∏ᶠ i, f i a
参数：hf : HasFiniteMulSupport f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasFiniteMulSupport.fun_comp`：∀ {α : Type u_1} {M : Type u_2} [
inst : One M] {N : Type u_3} [inst_1 : One N] {g : M → N} {f : α → M},   Functio
n.HasFiniteMulSupport f → g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `finprod_def`：finprod_def (f : α -> M) [Decidable (HasFiniteMulSupport f)
] : ∏ᶠ i : α, f i = if h : HasFiniteMulSupport f then ∏ i in h.toFinset, f i els
e…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
lemma finprod_apply {α ι : Type*} {f : ι → α → N} (hf : HasFiniteMulSupport f) (a : α) :
    (∏ᶠ i, f i) a = ∏ᶠ i, f i a := by
  classical
  have hf' : HasFiniteMulSupport fun i ↦ f i a := by fun_prop (disch := simp)
  simp only [finprod_def, dif_pos, hf, hf', Finset.prod_apply]
  symm
  apply Finset.prod_subset <;> aesop

@[to_additive]
/-
**Finset.mulSupport_of_fiberwise_prod_subset_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.mulSupport_of_fiberwise_prod_subset_image [DecidableEq β] (s : Fins
et α) (f : α -> M) (g : α -> β) : (mulSupport fun b => ∏ a in s with g a = b, f 
a) subseteq s.image g
参数：s : Finset α；f : α -> M；g : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.nonempty_of_prod_ne_one`：nonempty_of_prod_ne_one (h : ∏ x in s, f
 x != 1) : s.Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem Finset.mulSupport_of_fiberwise_prod_subset_image [DecidableEq β] (s : Finset α) (f : α → M)
    (g : α → β) : (mulSupport fun b ↦ ∏ a ∈ s with g a = b, f a) ⊆ s.image g := by
  simp only [Finset.coe_image]
  intro b h
  suffices {a ∈ s | g a = b}.Nonempty by
    simpa only [fiber_nonempty_iff_mem_image, Finset.mem_image, exists_prop]
  exact Finset.nonempty_of_prod_ne_one h

/-- Note that `b ∈ (s.filter (fun ab => Prod.fst ab = a)).image Prod.snd` iff `(a, b) ∈ s` so
we can simplify the right-hand side of this lemma. However the form stated here is more useful for
iterating this lemma, e.g., if we have `f : α × β × γ → M`. -/
@[to_additive
      /-- Note that `b ∈ (s.filter (fun ab => Prod.fst ab = a)).image Prod.snd` iff `(a, b) ∈ s` so
      we can simplify the right-hand side of this lemma. However the form stated here is more
      useful for iterating this lemma, e.g., if we have `f : α × β × γ → M`. -/]
/-
**finprod_mem_finset_product'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_finset_product' [DecidableEq α] [DecidableEq β] (s : Finset (α
 × β)) (f : α × β -> M) : (∏ᶠ (ab) (_ : ab in s), f ab) = ∏ᶠ (a) (b) (_ : b in (
s.filter fun ab => Prod.fst ab = a).image Prod.snd), f (a, b)
参数：s : Finset (α × β)；f : α × β -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_nbij'`：prod_nbij' (i : ι -> κ) (j : κ -> ι) (hi : forall a i
n s, i a in t) (hj : forall a in t, j a in s) (left_inv : forall a in s, j (i a)
 = a) (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `finprod_mem_finset_eq_prod`：finprod_mem_finset_eq_prod (f : α -> M) (s :
 Finset α) : ∏ᶠ i in s, f i = ∏ i in s, f i
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
· 使用定理 `Finset.mulSupport_of_fiberwise_prod_subset_image`：Finset.mulSupport_of_f
iberwise_prod_subset_image [DecidableEq β] (s : Finset α) (f : α -> M) (g : α ->
 β) : (mulSupport fun b => ∏ a in s wi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_fiberwise_of_maps_to`：prod_fiberwise_of_maps_to {g : ι -> κ}
 (h : forall i in s, g i in t) (f : ι -> M) : ∏ j in t, ∏ i in s with g i = j, f
 i = ∏ i in s, f i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem finprod_mem_finset_product' [DecidableEq α] [DecidableEq β] (s : Finset (α × β))
    (f : α × β → M) :
    (∏ᶠ (ab) (_ : ab ∈ s), f ab) =
      ∏ᶠ (a) (b) (_ : b ∈ (s.filter fun ab => Prod.fst ab = a).image Prod.snd), f (a, b) := by
  have (a : _) :
      ∏ i ∈ (s.filter fun ab => Prod.fst ab = a).image Prod.snd, f (a, i) =
        (s.filter (Prod.fst · = a)).prod f := by
    refine Finset.prod_nbij' (fun b ↦ (a, b)) Prod.snd ?_ ?_ ?_ ?_ ?_ <;> aesop
  rw [finprod_mem_finset_eq_prod]
  simp_rw [finprod_mem_finset_eq_prod, this]
  rw [finprod_eq_prod_of_mulSupport_subset _
      (s.mulSupport_of_fiberwise_prod_subset_image f Prod.fst),
    ← Finset.prod_fiberwise_of_maps_to (t := Finset.image Prod.fst s) _ f]
  -- `finish` could close the goal here
  simp only [Finset.mem_image]
  exact fun x hx => ⟨x, hx, rfl⟩

/-- See also `finprod_mem_finset_product'`. -/
@[to_additive /-- See also `finsum_mem_finset_product'`. -/]
/-
**finprod_mem_finset_product** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_finset_product (s : Finset (α × β)) (f : α × β -> M) : (∏ᶠ (ab
) (_ : ab in s), f ab) = ∏ᶠ (a) (b) (_ : (a, b) in s), f (a, b)
参数：s : Finset (α × β)；f : α × β -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_mem_finset_product'`：finprod_mem_finset_product' [DecidableEq α]
 [DecidableEq β] (s : Finset (α × β)) (f : α × β -> M) : (∏ᶠ (ab) (_ : ab in s),
 f ab) = ∏ᶠ (a) (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finprod_congr_Prop`：finprod_congr_Prop {p q : Prop} {f : p -> M} {g : q 
-> M} (hpq : p = q) (hfg : forall h : q, f (hpq.mpr h) = g h) : finprod f = finp
rod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See also `finprod_mem_finset_product'`.
-/
theorem finprod_mem_finset_product (s : Finset (α × β)) (f : α × β → M) :
    (∏ᶠ (ab) (_ : ab ∈ s), f ab) = ∏ᶠ (a) (b) (_ : (a, b) ∈ s), f (a, b) := by
  classical
    rw [finprod_mem_finset_product']
    simp

@[to_additive]
/-
**finprod_mem_finset_product** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_mem_finset_product (s : Finset (α × β)) (f : α × β -> M) : (∏ᶠ (ab
) (_ : ab in s), f ab) = ∏ᶠ (a) (b) (_ : (a, b) in s), f (a, b)
参数：s : Finset (α × β)；f : α × β -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_mem_finset_product'`：finprod_mem_finset_product' [DecidableEq α]
 [DecidableEq β] (s : Finset (α × β)) (f : α × β -> M) : (∏ᶠ (ab) (_ : ab in s),
 f ab) = ∏ᶠ (a) (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finprod_congr_Prop`：finprod_congr_Prop {p q : Prop} {f : p -> M} {g : q 
-> M} (hpq : p = q) (hfg : forall h : q, f (hpq.mpr h) = g h) : finprod f = finp
rod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finprod_mem_finset_product₃ {γ : Type*} (s : Finset (α × β × γ)) (f : α × β × γ → M) :
    (∏ᶠ (abc) (_ : abc ∈ s), f abc) = ∏ᶠ (a) (b) (c) (_ : (a, b, c) ∈ s), f (a, b, c) := by
  classical
    rw [finprod_mem_finset_product']
    simp_rw [finprod_mem_finset_product']
    simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**finprod_curry** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_curry (f : α × β -> M) (hf : HasFiniteMulSupport f) : ∏ᶠ ab, f ab 
= ∏ᶠ (a) (b), f (a, b)
参数：f : α × β -> M；hf : HasFiniteMulSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_congr_Prop`：finprod_congr_Prop {p q : Prop} {f : p -> M} {g : q 
-> M} (hpq : p = q) (hfg : forall h : q, f (hpq.mpr h) = g h) : finprod f = finp
rod g
· 使用定理 `finprod_apply_ne_one`：finprod_apply_ne_one (f : α -> M) (a : α) : ∏ᶠ _ :
 f a != 1, f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finprod_mem_finset_product`：finprod_mem_finset_product (s : Finset (α × 
β)) (f : α × β -> M) : (∏ᶠ (ab) (_ : ab in s), f ab) = ∏ᶠ (a) (b) (_ : (a, b) in
 s), f (a, b)
-/
theorem finprod_curry (f : α × β → M) (hf : HasFiniteMulSupport f) :
    ∏ᶠ ab, f ab = ∏ᶠ (a) (b), f (a, b) := by
  have h₁ : ∀ a, ∏ᶠ _ : a ∈ hf.toFinset, f a = f a := by simp
  have h₂ : ∏ᶠ a, f a = ∏ᶠ (a) (_ : a ∈ hf.toFinset), f a := by simp
  simp_rw [h₂, finprod_mem_finset_product, h₁]

@[to_additive]
/-
**finprod_curry** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_curry (f : α × β -> M) (hf : HasFiniteMulSupport f) : ∏ᶠ ab, f ab 
= ∏ᶠ (a) (b), f (a, b)
参数：f : α × β -> M；hf : HasFiniteMulSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_congr_Prop`：finprod_congr_Prop {p q : Prop} {f : p -> M} {g : q 
-> M} (hpq : p = q) (hfg : forall h : q, f (hpq.mpr h) = g h) : finprod f = finp
rod g
· 使用定理 `finprod_apply_ne_one`：finprod_apply_ne_one (f : α -> M) (a : α) : ∏ᶠ _ :
 f a != 1, f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finprod_mem_finset_product`：finprod_mem_finset_product (s : Finset (α × 
β)) (f : α × β -> M) : (∏ᶠ (ab) (_ : ab in s), f ab) = ∏ᶠ (a) (b) (_ : (a, b) in
 s), f (a, b)
-/
theorem finprod_curry₃ {γ : Type*} (f : α × β × γ → M) (h : HasFiniteMulSupport f) :
    ∏ᶠ abc, f abc = ∏ᶠ (a) (b) (c), f (a, b, c) := by
  rw [finprod_curry f h]
  congr
  ext a
  rw [finprod_curry]
  simp [h]

@[to_additive]
/-
**finprod_dmem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_dmem {s : Set α} [DecidablePred (· in s)] (f : forall a : α, a in 
s -> M) : (∏ᶠ (a : α) (h : a in s), f a h) = ∏ᶠ (a : α) (_ : a in s), if h' : a 
in s then f a h' else 1
参数：· in s；f : forall a : α, a in s -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_congr`：finprod_congr {f g : α -> M} (h : forall x, f x = g x) : 
finprod f = finprod g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem finprod_dmem {s : Set α} [DecidablePred (· ∈ s)] (f : ∀ a : α, a ∈ s → M) :
    (∏ᶠ (a : α) (h : a ∈ s), f a h) = ∏ᶠ (a : α) (_ : a ∈ s), if h' : a ∈ s then f a h' else 1 :=
  finprod_congr fun _ => finprod_congr fun ha => (dif_pos ha).symm

@[to_additive]
/-
**finprod_emb_domain'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_emb_domain' {f : α -> β} (hf : Injective f) [DecidablePred (· in S
et.range f)] (g : α -> M) : (∏ᶠ b : β, if h : b in Set.range f then g (Classical
.choose h) else 1) = ∏ᶠ a : α, g a
参数：hf : Injective f；· in Set.range f；g : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finprod_dmem`：finprod_dmem {s : Set α} [DecidablePred (· in s)] (f : for
all a : α, a in s -> M) : (∏ᶠ (a : α) (h : a in s), f a h) = ∏ᶠ (a : α) (_ : a i
n …
· 使用定理 `finprod_mem_range`：finprod_mem_range {g : β -> α} (hg : Injective g) : ∏
ᶠ i in range g, f i = ∏ᶠ j, f (g j)
· 使用定理 `finprod_congr`：finprod_congr {f g : α -> M} (h : forall x, f x = g x) : 
finprod f = finprod g
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem finprod_emb_domain' {f : α → β} (hf : Injective f) [DecidablePred (· ∈ Set.range f)]
    (g : α → M) :
    (∏ᶠ b : β, if h : b ∈ Set.range f then g (Classical.choose h) else 1) = ∏ᶠ a : α, g a := by
  simp_rw [← finprod_eq_dif]
  rw [finprod_dmem, finprod_mem_range hf, finprod_congr fun a => _]
  intro a
  rw [dif_pos (Set.mem_range_self a), hf (Classical.choose_spec (Set.mem_range_self a))]

@[to_additive]
/-
**finprod_emb_domain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_emb_domain (f : α ↪ β) [DecidablePred (· in Set.range f)] (g : α -
> M) : (∏ᶠ b : β, if h : b in Set.range f then g (Classical.choose h) else 1) = 
∏ᶠ a : α, g a
参数：f : α ↪ β；· in Set.range f；g : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_emb_domain'`：finprod_emb_domain' {f : α -> β} (hf : Injective f)
 [DecidablePred (· in Set.range f)] (g : α -> M) : (∏ᶠ b : β, if h : b in Set.ra
nge f the…
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem finprod_emb_domain (f : α ↪ β) [DecidablePred (· ∈ Set.range f)] (g : α → M) :
    (∏ᶠ b : β, if h : b ∈ Set.range f then g (Classical.choose h) else 1) = ∏ᶠ a : α, g a :=
  finprod_emb_domain' f.injective g

@[simp, norm_cast]
/-
**Nat.cast_finprod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.cast_finprod [Finite ι] {R : Type*} [CommSemiring R] (f : ι -> Nat) : 
↑(∏ᶠ x, f x : Nat) = ∏ᶠ x, (f x : R)
参数：f : ι -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_finprod`：MonoidHom.map_finprod {f : α -> M} (g : M ->* N) 
(hf : HasFiniteMulSupport f) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i)
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
lemma Nat.cast_finprod [Finite ι] {R : Type*} [CommSemiring R] (f : ι → ℕ) :
    ↑(∏ᶠ x, f x : ℕ) = ∏ᶠ x, (f x : R) :=
  (Nat.castRingHom R).map_finprod f.mulSupport.toFinite

/-- This version does not assume that `ι` is finite (compare `Nat.cast_finprod`), but instead needs
to assume characteristic zero to deal with the infinite case. -/
@[simp, norm_cast]
/-
**Nat.cast_finprod'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.cast_finprod' {R : Type*} [CommSemiring R] [CharZero R] (f : ι -> Nat)
 : (∏ᶠ (x : ι), f x : Nat) = ∏ᶠ (x : ι), (f x : R)
参数：f : ι -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finprod`：map_finprod {G : Type*} [FunLike G M N] [MonoidHomClass G M
 N] (g : G) (hf : HasFiniteMulSupport f) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Function.HasFiniteMulSupport.of_comp`：∀ {α : Type u_1} {M : Type u_2} [i
nst : One M] {β : Type u_3} {f : β → M} {g : α → β} [inst_1 : One β],   Function
.HasFiniteMulSupport (f ∘ …
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_of_not_hasFiniteMulSupport`：finprod_of_not_hasFiniteMulSupport {
f : α -> M} (hf : ¬ f.HasFiniteMulSupport) : ∏ᶠ i, f i = 1

--- 原说明 ---
This version does not assume that `ι` is finite (compare `Nat.cast_finprod`), bu
t instead needs
to assume characteristic zero to deal with the infinite case.
-/
lemma Nat.cast_finprod' {R : Type*} [CommSemiring R] [CharZero R] (f : ι → ℕ) :
    (∏ᶠ (x : ι), f x : ℕ) = ∏ᶠ (x : ι), (f x : R) := by
  by_cases hf : f.HasFiniteMulSupport
  · exact map_finprod (Nat.castRingHom R) hf
  · have H : ¬ (fun i ↦ (f i : R)).HasFiniteMulSupport :=
      fun h ↦ hf <| h.of_comp cast_one cast_injective
    rw [finprod_of_not_hasFiniteMulSupport hf, finprod_of_not_hasFiniteMulSupport H, cast_one]

@[simp, norm_cast]
/-
**Nat.cast_finprod_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.cast_finprod_mem {s : Set ι} (hs : s.Finite) {R : Type*} [CommSemiring
 R] (f : ι -> Nat) : ↑(∏ᶠ x in s, f x : Nat) = ∏ᶠ x in s, (f x : R)
参数：hs : s.Finite；f : ι -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_finprod_mem`：MonoidHom.map_finprod_mem (f : α -> M) (g : M
 ->* N) (hs : s.Finite) : g (∏ᶠ j in s, f j) = ∏ᶠ i in s, g (f i)
-/
lemma Nat.cast_finprod_mem {s : Set ι} (hs : s.Finite) {R : Type*} [CommSemiring R] (f : ι → ℕ) :
    ↑(∏ᶠ x ∈ s, f x : ℕ) = ∏ᶠ x ∈ s, (f x : R) :=
  (Nat.castRingHom R).map_finprod_mem _ hs

@[simp, norm_cast]
/-
**Nat.cast_finsum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.cast_finsum [Finite ι] {M : Type*} [AddCommMonoidWithOne M] (f : ι -> 
Nat) : ↑(∑ᶠ x, f x : Nat) = ∑ᶠ x, (f x : M)
参数：f : ι -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_finsum`：∀ {α : Type u_1} {M : Type u_5} {N : Type u_6} 
[inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] {f : α → M}   (g : M →+ N), 
Function.HasF…
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
lemma Nat.cast_finsum [Finite ι] {M : Type*} [AddCommMonoidWithOne M]
    (f : ι → ℕ) : ↑(∑ᶠ x, f x : ℕ) = ∑ᶠ x, (f x : M) :=
  (Nat.castAddMonoidHom M).map_finsum f.support.toFinite

@[simp, norm_cast]
/-
**Nat.cast_finsum_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.cast_finsum_mem {s : Set ι} (hs : s.Finite) {M : Type*} [AddCommMonoid
WithOne M] (f : ι -> Nat) : ↑(∑ᶠ x in s, f x : Nat) = ∑ᶠ x in s, (f x : M)
参数：hs : s.Finite；f : ι -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_finsum_mem`：∀ {α : Type u_1} {M : Type u_5} {N : Type u
_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] {s : Set α}   (f : α → M
) (g : M →+ N), s…
-/
lemma Nat.cast_finsum_mem {s : Set ι} (hs : s.Finite) {M : Type*}
    [AddCommMonoidWithOne M] (f : ι → ℕ) : ↑(∑ᶠ x ∈ s, f x : ℕ) = ∑ᶠ x ∈ s, (f x : M) :=
  (Nat.castAddMonoidHom M).map_finsum_mem _ hs

end type

/-!
### Some API for `fun a ↦ f a ^ count a s` on multisets
-/

namespace Multiset

variable {α M : Type*} [DecidableEq α] [CommMonoid M]

@[to_additive]
/-
**Multiset.mulSupport_fun_pow_count_subset** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：mulSupport_fun_pow_count_subset (s : Multiset α) (f : α -> M) : (fun a => 
f a ^ count a s).mulSupport subseteq s.toFinset
参数：s : Multiset α；f : α -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma mulSupport_fun_pow_count_subset (s : Multiset α) (f : α → M) :
    (fun a ↦ f a ^ count a s).mulSupport ⊆ s.toFinset := by
  simp +contextual [not_imp_comm]

@[to_additive (attr := fun_prop)]
/-
**Multiset.hasFiniteMulSupport_fun_pow_count** 是 Mathlib 中的一个引理，位于命名空间 `Multiset
`。
形式化陈述：hasFiniteMulSupport_fun_pow_count (s : Multiset α) (f : α -> M) : (fun a =
> (f a) ^ s.count a).HasFiniteMulSupport
参数：s : Multiset α；f : α -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用引理 `Multiset.mulSupport_fun_pow_count_subset`：mulSupport_fun_pow_count_subse
t (s : Multiset α) (f : α -> M) : (fun a => f a ^ count a s).mulSupport subseteq
 s.toFinset
-/
lemma hasFiniteMulSupport_fun_pow_count (s : Multiset α) (f : α → M) :
    (fun a ↦ (f a) ^ s.count a).HasFiniteMulSupport :=
  s.toFinset.finite_toSet.subset <| mulSupport_fun_pow_count_subset ..

@[to_additive]
/-
**Multiset.prod_map_eq_finprod** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_map_eq_finprod (s : Multiset α) (f : α -> M) : (s.map f).prod = ∏ᶠ a,
 f a ^ s.count a
参数：s : Multiset α；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_multiset_map_count`：prod_multiset_map_count [DecidableEq ι] 
(s : Multiset ι) {M : Type*} [CommMonoid M] (f : ι -> M) : (s.map f).prod = ∏ m 
in s.toFinset, f m ^…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
· 使用引理 `Multiset.mulSupport_fun_pow_count_subset`：mulSupport_fun_pow_count_subse
t (s : Multiset α) (f : α -> M) : (fun a => f a ^ count a s).mulSupport subseteq
 s.toFinset
-/
lemma prod_map_eq_finprod (s : Multiset α) (f : α → M) :
    (s.map f).prod = ∏ᶠ a, f a ^ s.count a := by
  rw [Finset.prod_multiset_map_count, eq_comm]
  exact finprod_eq_prod_of_mulSupport_subset _ <| mulSupport_fun_pow_count_subset ..

end Multiset

