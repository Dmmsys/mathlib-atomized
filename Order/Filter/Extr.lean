/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Minimum and maximum w.r.t. a filter and on a set

## Main Definitions

This file defines six predicates of the form `isAB`, where `A` is `Min`, `Max`, or `Extr`,
and `B` is `Filter` or `On`.

* `isMinFilter f l a` means that `f a ≤ f x` in some `l`-neighborhood of `a`;
* `isMaxFilter f l a` means that `f x ≤ f a` in some `l`-neighborhood of `a`;
* `isExtrFilter f l a` means `isMinFilter f l a` or `isMaxFilter f l a`.

Similar predicates with `on` suffix are particular cases for `l = 𝓟 s`.

## Main statements

### Change of the filter (set) argument

* `is*Filter.filter_mono` : replace the filter with a smaller one;
* `is*Filter.filter_inf` : replace a filter `l` with `l ⊓ l'`;
* `is*On.on_subset` : restrict to a smaller set;
* `is*Pn.inter` : replace a set `s` with `s ∩ t`.

### Composition

* `is**.comp_mono` : if `x` is an extremum for `f` and `g` is a monotone function,
  then `x` is an extremum for `g ∘ f`;
* `is**.comp_antitone` : similarly for the case of antitone `g`;
* `is**.bicomp_mono` : if `x` is an extremum of the same type for `f` and `g`
  and a binary operation `op` is monotone in both arguments, then `x` is an extremum
  of the same type for `fun x => op (f x) (g x)`.
* `is*Filter.comp_tendsto` : if `g x` is an extremum for `f` w.r.t. `l'` and `Tendsto g l l'`,
  then `x` is an extremum for `f ∘ g` w.r.t. `l`.
* `is*On.on_preimage` : if `g x` is an extremum for `f` on `s`, then `x` is an extremum
  for `f ∘ g` on `g ⁻¹' s`.

### Algebraic operations

* `is**.add` : if `x` is an extremum of the same type for two functions,
  then it is an extremum of the same type for their sum;
* `is**.neg` : if `x` is an extremum for `f`, then it is an extremum
  of the opposite type for `-f`;
* `is**.sub` : if `x` is a minimum for `f` and a maximum for `g`,
  then it is a minimum for `f - g` and a maximum for `g - f`;
* `is**.max`, `is**.min`, `is**.sup`, `is**.inf` : similarly for `is**.add`
  for pointwise `max`, `min`, `sup`, `inf`, respectively.


### Miscellaneous definitions

* `is**_const` : any point is both a minimum and maximum for a constant function;
* `isMin/Max*.isExt` : any minimum/maximum point is an extremum;
* `is**.dual`, `is**.undual`: conversion between codomains `α` and `dual α`;

## Missing features (TODO)

* Multiplication and division;
* `is**.bicompl` : if `x` is a minimum for `f`, `y` is a minimum for `g`, and `op` is a monotone
  binary operation, then `(x, y)` is a minimum for `uncurry (bicompl op f g)`. From this point
  of view, `is**.bicomp` is a composition
* It would be nice to have a tactic that specializes `comp_(anti)mono` or `bicomp_mono`
  based on a proof of monotonicity of a given (binary) function. The tactic should maintain a `meta`
  list of known (anti)monotone (binary) functions with their names, as well as a list of special
  types of filters, and define the missing lemmas once one of these two lists grows.
-/

@[expose] public section


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

open Set Filter Relator

section Preorder

variable [Preorder β] [Preorder γ]
variable (f : α -> β) (s : Set α) (l : Filter α) (a : α)

/-! ### Definitions -/


/--
Definition of `IsMinFilter` / `IsMinFilter` 的定义

English:
definition IsMinFilter
  signature: : Prop
  body: forallᶠ x in l, f a <= f x

中文:
定义 IsMinFilter
  签名: : 命题
  定义体: forallᶠ x in l, f a <= f x
-/
def IsMinFilter : Prop :=
  forallᶠ x in l, f a <= f x

/--
Definition of `IsMaxFilter` / `IsMaxFilter` 的定义

English:
definition IsMaxFilter
  signature: : Prop
  body: forallᶠ x in l, f x <= f a

中文:
定义 IsMaxFilter
  签名: : 命题
  定义体: forallᶠ x in l, f x <= f a
-/
def IsMaxFilter : Prop :=
  forallᶠ x in l, f x <= f a

/--
Definition of `IsExtrFilter` / `IsExtrFilter` 的定义

English:
definition IsExtrFilter
  signature: : Prop
  body: IsMinFilter f l a ∨ IsMaxFilter f l a

中文:
定义 IsExtrFilter
  签名: : 命题
  定义体: IsMinFilter f l a ∨ IsMaxFilter f l a

Depends on / 依赖: IsMaxFilter, IsMinFilter
-/
def IsExtrFilter : Prop :=
  IsMinFilter f l a ∨ IsMaxFilter f l a

/--
Definition of `IsMinOn` / `IsMinOn` 的定义

English:
definition IsMinOn
  body: IsMinFilter f (𝓟 s) a

中文:
定义 IsMinOn
  定义体: IsMinFilter f (𝓟 s) a

Depends on / 依赖: IsMinFilter
-/
def IsMinOn :=
  IsMinFilter f (𝓟 s) a

/--
Definition of `IsMaxOn` / `IsMaxOn` 的定义

English:
definition IsMaxOn
  body: IsMaxFilter f (𝓟 s) a

中文:
定义 IsMaxOn
  定义体: IsMaxFilter f (𝓟 s) a

Depends on / 依赖: IsMaxFilter
-/
def IsMaxOn :=
  IsMaxFilter f (𝓟 s) a

/-- `IsExtrOn f s a` means `IsMinOn f s a` or `IsMaxOn f s a` -/
@[wikidata Q845060]
/--
Definition of `IsExtrOn` / `IsExtrOn` 的定义

English:
definition IsExtrOn
  signature: : Prop
  body: IsExtrFilter f (𝓟 s) a

中文:
定义 IsExtrOn
  签名: : 命题
  定义体: IsExtrFilter f (𝓟 s) a

Depends on / 依赖: IsExtrFilter
-/
def IsExtrOn : Prop :=
  IsExtrFilter f (𝓟 s) a

variable {f s a l} {t : Set α} {l' : Filter α}

/--
theorem `IsExtrOn.elim` / 定理 `IsExtrOn.elim`

English:
theorem IsExtrOn.elim
  given: {p : Prop}
  statement: IsExtrOn f s a -> (IsMinOn f s a -> p) -> (IsMaxOn f s a -> p) -> p
  proof: Or.elim

中文:
定理 IsExtrOn.elim
  条件: {p : 命题}
  结论: IsExtrOn f s a -> (IsMinOn f s a -> p) -> (IsMaxOn f s a -> p) -> p
  证明: Or.elim

Depends on / 依赖: Or.elim
-/
theorem IsExtrOn.elim {p : Prop} : IsExtrOn f s a -> (IsMinOn f s a -> p) -> (IsMaxOn f s a -> p) -> p :=
  Or.elim

/--
theorem `isMinOn_iff` / 定理 `isMinOn_iff`

English:
theorem isMinOn_iff
  statement: IsMinOn f s a ↔ forall x in s, f a <= f x
  proof: Iff.rfl

中文:
定理 isMinOn_iff
  结论: IsMinOn f s a ↔ 对任意 x in s, f a <= f x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isMinOn_iff : IsMinOn f s a ↔ forall x in s, f a <= f x :=
  Iff.rfl

/--
theorem `isMaxOn_iff` / 定理 `isMaxOn_iff`

English:
theorem isMaxOn_iff
  statement: IsMaxOn f s a ↔ forall x in s, f x <= f a
  proof: Iff.rfl

中文:
定理 isMaxOn_iff
  结论: IsMaxOn f s a ↔ 对任意 x in s, f x <= f a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isMaxOn_iff : IsMaxOn f s a ↔ forall x in s, f x <= f a :=
  Iff.rfl

/--
theorem `isMinOn_univ_iff` / 定理 `isMinOn_univ_iff`

English:
theorem isMinOn_univ_iff
  statement: IsMinOn f univ a ↔ forall x, f a <= f x
  proof: univ_subset_iff.trans eq_univ_iff_forall

中文:
定理 isMinOn_univ_iff
  结论: IsMinOn f univ a ↔ 对任意 x, f a <= f x
  证明: univ_subset_iff.trans eq_univ_iff_forall

Depends on / 依赖: eq_univ_iff_forall, univ_subset_iff, univ_subset_iff.trans
-/
theorem isMinOn_univ_iff : IsMinOn f univ a ↔ forall x, f a <= f x :=
  univ_subset_iff.trans eq_univ_iff_forall

/--
theorem `isMaxOn_univ_iff` / 定理 `isMaxOn_univ_iff`

English:
theorem isMaxOn_univ_iff
  statement: IsMaxOn f univ a ↔ forall x, f x <= f a
  proof: univ_subset_iff.trans eq_univ_iff_forall

中文:
定理 isMaxOn_univ_iff
  结论: IsMaxOn f univ a ↔ 对任意 x, f x <= f a
  证明: univ_subset_iff.trans eq_univ_iff_forall

Depends on / 依赖: eq_univ_iff_forall, univ_subset_iff, univ_subset_iff.trans
-/
theorem isMaxOn_univ_iff : IsMaxOn f univ a ↔ forall x, f x <= f a :=
  univ_subset_iff.trans eq_univ_iff_forall

/--
theorem `IsMinOn.bddBelow` / 定理 `IsMinOn.bddBelow`

English:
theorem IsMinOn.bddBelow
  given: (h : IsMinOn f s a)
  proof: ⟨f a, by simpa [mem_lowerBounds] using! h⟩

中文:
定理 IsMinOn.bddBelow
  条件: (h : IsMinOn f s a)
  证明: ⟨f a, by simpa [mem_lowerBounds] using! h⟩

Depends on / 依赖: mem_lowerBounds
-/
theorem IsMinOn.bddBelow (h : IsMinOn f s a) :
    BddBelow (f '' s) :=
  ⟨f a, by simpa [mem_lowerBounds] using! h⟩

/--
theorem `IsMinOn.isGLB` / 定理 `IsMinOn.isGLB`

English:
theorem IsMinOn.isGLB
  given: (ha : a in s) (hfsa : IsMinOn f s a)
  proof: by
  rw [isGLB_iff_le_iff]
  intro b
  simp only [mem_lowerBounds, mem_ofPred_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact ⟨fun hba x hx => le_trans hba (hfsa hx), fun hb => hb a ha⟩

中文:
定理 IsMinOn.isGLB
  条件: (ha : a in s) (hfsa : IsMinOn f s a)
  证明: by
  rw [isGLB_iff_le_iff]
  intro b
  simp only [mem_lowerBounds, mem_ofPred_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact ⟨fun hba x hx => le_trans hba (hfsa hx), fun hb => hb a ha⟩

Depends on / 依赖: and_imp, forall_exists_index, isGLB_iff_le_iff, le_trans, mem_lowerBounds, mem_ofPred_eq
-/
theorem IsMinOn.isGLB (ha : a in s) (hfsa : IsMinOn f s a) :
    IsGLB {f x | x in s} (f a) := by
  rw [isGLB_iff_le_iff]
  intro b
  simp only [mem_lowerBounds, mem_ofPred_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact ⟨fun hba x hx => le_trans hba (hfsa hx), fun hb => hb a ha⟩

/--
theorem `IsMaxOn.isLUB` / 定理 `IsMaxOn.isLUB`

English:
theorem IsMaxOn.isLUB
  given: (ha : a in s) (hfsa : IsMaxOn f s a)
  proof: IsMinOn.isGLB (α := αᵒᵈ) (β := βᵒᵈ) ha hfsa

中文:
定理 IsMaxOn.isLUB
  条件: (ha : a in s) (hfsa : IsMaxOn f s a)
  证明: IsMinOn.isGLB (α := αᵒᵈ) (β := βᵒᵈ) ha hfsa

Depends on / 依赖: IsMinOn, IsMinOn.isGLB
-/
theorem IsMaxOn.isLUB (ha : a in s) (hfsa : IsMaxOn f s a) :
    IsLUB {f x | x in s} (f a) :=
  IsMinOn.isGLB (α := αᵒᵈ) (β := βᵒᵈ) ha hfsa

/--
theorem `IsMaxOn.bddAbove` / 定理 `IsMaxOn.bddAbove`

English:
theorem IsMaxOn.bddAbove
  given: (h : IsMaxOn f s a)
  proof: ⟨f a, by simpa [mem_upperBounds] using! h⟩

中文:
定理 IsMaxOn.bddAbove
  条件: (h : IsMaxOn f s a)
  证明: ⟨f a, by simpa [mem_upperBounds] using! h⟩

Depends on / 依赖: mem_upperBounds
-/
theorem IsMaxOn.bddAbove (h : IsMaxOn f s a) :
    BddAbove (f '' s) :=
  ⟨f a, by simpa [mem_upperBounds] using! h⟩

/--
theorem `IsMinFilter.tendsto_principal_Ici` / 定理 `IsMinFilter.tendsto_principal_Ici`

English:
theorem IsMinFilter.tendsto_principal_Ici
  given: (h : IsMinFilter f l a)
  statement: Tendsto f l (𝓟 <| Ici (f a))
  proof: tendsto_principal.2 h

中文:
定理 IsMinFilter.tendsto_principal_Ici
  条件: (h : IsMinFilter f l a)
  结论: Tendsto f l (𝓟 <| Ici (f a))
  证明: tendsto_principal.2 h

Depends on / 依赖: tendsto_principal
-/
theorem IsMinFilter.tendsto_principal_Ici (h : IsMinFilter f l a) : Tendsto f l (𝓟 <| Ici (f a)) :=
  tendsto_principal.2 h

/--
theorem `IsMaxFilter.tendsto_principal_Iic` / 定理 `IsMaxFilter.tendsto_principal_Iic`

English:
theorem IsMaxFilter.tendsto_principal_Iic
  given: (h : IsMaxFilter f l a)
  statement: Tendsto f l (𝓟 <| Iic (f a))
  proof: tendsto_principal.2 h

中文:
定理 IsMaxFilter.tendsto_principal_Iic
  条件: (h : IsMaxFilter f l a)
  结论: Tendsto f l (𝓟 <| Iic (f a))
  证明: tendsto_principal.2 h

Depends on / 依赖: tendsto_principal
-/
theorem IsMaxFilter.tendsto_principal_Iic (h : IsMaxFilter f l a) : Tendsto f l (𝓟 <| Iic (f a)) :=
  tendsto_principal.2 h



/--
theorem `IsMinFilter.isExtr` / 定理 `IsMinFilter.isExtr`

English:
theorem IsMinFilter.isExtr
  statement: IsMinFilter f l a -> IsExtrFilter f l a
  proof: Or.inl

中文:
定理 IsMinFilter.isExtr
  结论: IsMinFilter f l a -> IsExtrFilter f l a
  证明: Or.inl

Depends on / 依赖: Or.inl
-/
theorem IsMinFilter.isExtr : IsMinFilter f l a -> IsExtrFilter f l a :=
  Or.inl

/--
theorem `IsMaxFilter.isExtr` / 定理 `IsMaxFilter.isExtr`

English:
theorem IsMaxFilter.isExtr
  statement: IsMaxFilter f l a -> IsExtrFilter f l a
  proof: Or.inr

中文:
定理 IsMaxFilter.isExtr
  结论: IsMaxFilter f l a -> IsExtrFilter f l a
  证明: Or.inr

Depends on / 依赖: Or.inr
-/
theorem IsMaxFilter.isExtr : IsMaxFilter f l a -> IsExtrFilter f l a :=
  Or.inr

/--
theorem `IsMinOn.isExtr` / 定理 `IsMinOn.isExtr`

English:
theorem IsMinOn.isExtr
  given: (h : IsMinOn f s a)
  statement: IsExtrOn f s a
  proof: IsMinFilter.isExtr h

中文:
定理 IsMinOn.isExtr
  条件: (h : IsMinOn f s a)
  结论: IsExtrOn f s a
  证明: IsMinFilter.isExtr h

Depends on / 依赖: IsMinFilter, IsMinFilter.isExtr, isExtr
-/
theorem IsMinOn.isExtr (h : IsMinOn f s a) : IsExtrOn f s a :=
  IsMinFilter.isExtr h

/--
theorem `IsMaxOn.isExtr` / 定理 `IsMaxOn.isExtr`

English:
theorem IsMaxOn.isExtr
  given: (h : IsMaxOn f s a)
  statement: IsExtrOn f s a
  proof: IsMaxFilter.isExtr h

中文:
定理 IsMaxOn.isExtr
  条件: (h : IsMaxOn f s a)
  结论: IsExtrOn f s a
  证明: IsMaxFilter.isExtr h

Depends on / 依赖: IsMaxFilter, IsMaxFilter.isExtr, isExtr
-/
theorem IsMaxOn.isExtr (h : IsMaxOn f s a) : IsExtrOn f s a :=
  IsMaxFilter.isExtr h



/--
theorem `isMinFilter_const` / 定理 `isMinFilter_const`

English:
theorem isMinFilter_const
  given: {b : β}
  statement: IsMinFilter (fun _ => b) l a
  proof: univ_mem' fun _ => le_rfl

中文:
定理 isMinFilter_const
  条件: {b : β}
  结论: IsMinFilter (fun _ => b) l a
  证明: univ_mem' fun _ => le_rfl

Depends on / 依赖: le_rfl, univ_mem
-/
theorem isMinFilter_const {b : β} : IsMinFilter (fun _ => b) l a :=
  univ_mem' fun _ => le_rfl

/--
theorem `isMaxFilter_const` / 定理 `isMaxFilter_const`

English:
theorem isMaxFilter_const
  given: {b : β}
  statement: IsMaxFilter (fun _ => b) l a
  proof: univ_mem' fun _ => le_rfl

中文:
定理 isMaxFilter_const
  条件: {b : β}
  结论: IsMaxFilter (fun _ => b) l a
  证明: univ_mem' fun _ => le_rfl

Depends on / 依赖: le_rfl, univ_mem
-/
theorem isMaxFilter_const {b : β} : IsMaxFilter (fun _ => b) l a :=
  univ_mem' fun _ => le_rfl

/--
theorem `isExtrFilter_const` / 定理 `isExtrFilter_const`

English:
theorem isExtrFilter_const
  given: {b : β}
  statement: IsExtrFilter (fun _ => b) l a
  proof: isMinFilter_const.isExtr

中文:
定理 isExtrFilter_const
  条件: {b : β}
  结论: IsExtrFilter (fun _ => b) l a
  证明: isMinFilter_const.isExtr

Depends on / 依赖: isExtr, isMinFilter_const, isMinFilter_const.isExtr
-/
theorem isExtrFilter_const {b : β} : IsExtrFilter (fun _ => b) l a :=
  isMinFilter_const.isExtr

/--
theorem `isMinOn_const` / 定理 `isMinOn_const`

English:
theorem isMinOn_const
  given: {b : β}
  statement: IsMinOn (fun _ => b) s a
  proof: isMinFilter_const

中文:
定理 isMinOn_const
  条件: {b : β}
  结论: IsMinOn (fun _ => b) s a
  证明: isMinFilter_const

Depends on / 依赖: isMinFilter_const
-/
theorem isMinOn_const {b : β} : IsMinOn (fun _ => b) s a :=
  isMinFilter_const

/--
theorem `isMaxOn_const` / 定理 `isMaxOn_const`

English:
theorem isMaxOn_const
  given: {b : β}
  statement: IsMaxOn (fun _ => b) s a
  proof: isMaxFilter_const

中文:
定理 isMaxOn_const
  条件: {b : β}
  结论: IsMaxOn (fun _ => b) s a
  证明: isMaxFilter_const

Depends on / 依赖: isMaxFilter_const
-/
theorem isMaxOn_const {b : β} : IsMaxOn (fun _ => b) s a :=
  isMaxFilter_const

/--
theorem `isExtrOn_const` / 定理 `isExtrOn_const`

English:
theorem isExtrOn_const
  given: {b : β}
  statement: IsExtrOn (fun _ => b) s a
  proof: isExtrFilter_const

中文:
定理 isExtrOn_const
  条件: {b : β}
  结论: IsExtrOn (fun _ => b) s a
  证明: isExtrFilter_const

Depends on / 依赖: isExtrFilter_const
-/
theorem isExtrOn_const {b : β} : IsExtrOn (fun _ => b) s a :=
  isExtrFilter_const

/--
lemma `eventuallyEq_of_isMinFilter_of_isMaxFilter` / 引理 `eventuallyEq_of_isMinFilter_of_isMaxFilter`

English:
lemma eventuallyEq_of_isMinFilter_of_isMaxFilter
  statement: {β : Type*} [PartialOrder β] {f : α -> β}
  proof: by
  filter_upwards [h₁, h₂] using by grind

中文:
引理 eventuallyEq_of_isMinFilter_of_isMaxFilter
  结论: {β : 类型} [PartialOrder β] {f : α -> β}
  证明: by
  filter_upwards [h₁, h₂] using by grind

Depends on / 依赖: filter_upwards
-/
lemma eventuallyEq_of_isMinFilter_of_isMaxFilter {β : Type*} [PartialOrder β] {f : α -> β}
    (h₁ : IsMinFilter f l a) (h₂ : IsMaxFilter f l a) : f =ᶠ[l] (fun _ => f a) := by
  filter_upwards [h₁, h₂] using by grind

/-! ### Order dual -/


open OrderDual (toDual)

/--
theorem `isMinFilter_dual_iff` / 定理 `isMinFilter_dual_iff`

English:
theorem isMinFilter_dual_iff
  statement: IsMinFilter (toDual ∘ f) l a ↔ IsMaxFilter f l a
  proof: Iff.rfl

中文:
定理 isMinFilter_dual_iff
  结论: IsMinFilter (toDual ∘ f) l a ↔ IsMaxFilter f l a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isMinFilter_dual_iff : IsMinFilter (toDual ∘ f) l a ↔ IsMaxFilter f l a :=
  Iff.rfl

/--
theorem `isMaxFilter_dual_iff` / 定理 `isMaxFilter_dual_iff`

English:
theorem isMaxFilter_dual_iff
  statement: IsMaxFilter (toDual ∘ f) l a ↔ IsMinFilter f l a
  proof: Iff.rfl

中文:
定理 isMaxFilter_dual_iff
  结论: IsMaxFilter (toDual ∘ f) l a ↔ IsMinFilter f l a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isMaxFilter_dual_iff : IsMaxFilter (toDual ∘ f) l a ↔ IsMinFilter f l a :=
  Iff.rfl

/--
theorem `isExtrFilter_dual_iff` / 定理 `isExtrFilter_dual_iff`

English:
theorem isExtrFilter_dual_iff
  statement: IsExtrFilter (toDual ∘ f) l a ↔ IsExtrFilter f l a
  proof: or_comm

alias ⟨IsMinFilter.undual, IsMaxFilter.dual⟩ := isMinFilter_dual_iff

alias ⟨IsMaxFilter.undual, IsMinFilter.dual⟩ := isMaxFilter_dual_iff

alias ⟨IsExtrFilter.undual, IsExtrFilter.dual⟩ := isExtrFilter_dual_iff

中文:
定理 isExtrFilter_dual_iff
  结论: IsExtrFilter (toDual ∘ f) l a ↔ IsExtrFilter f l a
  证明: or_comm

alias ⟨IsMinFilter.undual, IsMaxFilter.dual⟩ := isMinFilter_dual_iff

alias ⟨IsMaxFilter.undual, IsMinFilter.dual⟩ := isMaxFilter_dual_iff

alias ⟨IsExtrFilter.undual, IsExtrFilter.dual⟩ := isExtrFilter_dual_iff

Depends on / 依赖: or_comm
-/
theorem isExtrFilter_dual_iff : IsExtrFilter (toDual ∘ f) l a ↔ IsExtrFilter f l a :=
  or_comm

alias ⟨IsMinFilter.undual, IsMaxFilter.dual⟩ := isMinFilter_dual_iff

alias ⟨IsMaxFilter.undual, IsMinFilter.dual⟩ := isMaxFilter_dual_iff

alias ⟨IsExtrFilter.undual, IsExtrFilter.dual⟩ := isExtrFilter_dual_iff

/--
theorem `isMinOn_dual_iff` / 定理 `isMinOn_dual_iff`

English:
theorem isMinOn_dual_iff
  statement: IsMinOn (toDual ∘ f) s a ↔ IsMaxOn f s a
  proof: Iff.rfl

中文:
定理 isMinOn_dual_iff
  结论: IsMinOn (toDual ∘ f) s a ↔ IsMaxOn f s a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isMinOn_dual_iff : IsMinOn (toDual ∘ f) s a ↔ IsMaxOn f s a :=
  Iff.rfl

/--
theorem `isMaxOn_dual_iff` / 定理 `isMaxOn_dual_iff`

English:
theorem isMaxOn_dual_iff
  statement: IsMaxOn (toDual ∘ f) s a ↔ IsMinOn f s a
  proof: Iff.rfl

中文:
定理 isMaxOn_dual_iff
  结论: IsMaxOn (toDual ∘ f) s a ↔ IsMinOn f s a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isMaxOn_dual_iff : IsMaxOn (toDual ∘ f) s a ↔ IsMinOn f s a :=
  Iff.rfl

/--
theorem `isExtrOn_dual_iff` / 定理 `isExtrOn_dual_iff`

English:
theorem isExtrOn_dual_iff
  statement: IsExtrOn (toDual ∘ f) s a ↔ IsExtrOn f s a
  proof: or_comm

alias ⟨IsMinOn.undual, IsMaxOn.dual⟩ := isMinOn_dual_iff

alias ⟨IsMaxOn.undual, IsMinOn.dual⟩ := isMaxOn_dual_iff

alias ⟨IsExtrOn.undual, IsExtrOn.dual⟩ := isExtrOn_dual_iff

中文:
定理 isExtrOn_dual_iff
  结论: IsExtrOn (toDual ∘ f) s a ↔ IsExtrOn f s a
  证明: or_comm

alias ⟨IsMinOn.undual, IsMaxOn.dual⟩ := isMinOn_dual_iff

alias ⟨IsMaxOn.undual, IsMinOn.dual⟩ := isMaxOn_dual_iff

alias ⟨IsExtrOn.undual, IsExtrOn.dual⟩ := isExtrOn_dual_iff

Depends on / 依赖: or_comm
-/
theorem isExtrOn_dual_iff : IsExtrOn (toDual ∘ f) s a ↔ IsExtrOn f s a :=
  or_comm

alias ⟨IsMinOn.undual, IsMaxOn.dual⟩ := isMinOn_dual_iff

alias ⟨IsMaxOn.undual, IsMinOn.dual⟩ := isMaxOn_dual_iff

alias ⟨IsExtrOn.undual, IsExtrOn.dual⟩ := isExtrOn_dual_iff



/--
theorem `IsMinFilter.filter_mono` / 定理 `IsMinFilter.filter_mono`

English:
theorem IsMinFilter.filter_mono
  given: (h : IsMinFilter f l a) (hl : l' <= l)
  statement: IsMinFilter f l' a
  proof: hl h

中文:
定理 IsMinFilter.filter_mono
  条件: (h : IsMinFilter f l a) (hl : l' <= l)
  结论: IsMinFilter f l' a
  证明: hl h
-/
theorem IsMinFilter.filter_mono (h : IsMinFilter f l a) (hl : l' <= l) : IsMinFilter f l' a :=
  hl h

/--
theorem `IsMaxFilter.filter_mono` / 定理 `IsMaxFilter.filter_mono`

English:
theorem IsMaxFilter.filter_mono
  given: (h : IsMaxFilter f l a) (hl : l' <= l)
  statement: IsMaxFilter f l' a
  proof: hl h

中文:
定理 IsMaxFilter.filter_mono
  条件: (h : IsMaxFilter f l a) (hl : l' <= l)
  结论: IsMaxFilter f l' a
  证明: hl h
-/
theorem IsMaxFilter.filter_mono (h : IsMaxFilter f l a) (hl : l' <= l) : IsMaxFilter f l' a :=
  hl h

/--
theorem `IsExtrFilter.filter_mono` / 定理 `IsExtrFilter.filter_mono`

English:
theorem IsExtrFilter.filter_mono
  given: (h : IsExtrFilter f l a) (hl : l' <= l)
  statement: IsExtrFilter f l' a
  proof: h.elim (fun h => (h.filter_mono hl).isExtr) fun h => (h.filter_mono hl).isExtr

中文:
定理 IsExtrFilter.filter_mono
  条件: (h : IsExtrFilter f l a) (hl : l' <= l)
  结论: IsExtrFilter f l' a
  证明: h.elim (fun h => (h.filter_mono hl).isExtr) fun h => (h.filter_mono hl).isExtr

Depends on / 依赖: filter_mono, h.elim, h.filter_mono, isExtr
-/
theorem IsExtrFilter.filter_mono (h : IsExtrFilter f l a) (hl : l' <= l) : IsExtrFilter f l' a :=
  h.elim (fun h => (h.filter_mono hl).isExtr) fun h => (h.filter_mono hl).isExtr

/--
theorem `IsMinFilter.filter_inf` / 定理 `IsMinFilter.filter_inf`

English:
theorem IsMinFilter.filter_inf
  given: (h : IsMinFilter f l a) (l')
  statement: IsMinFilter f (l ⊓ l') a
  proof: h.filter_mono inf_le_left

中文:
定理 IsMinFilter.filter_inf
  条件: (h : IsMinFilter f l a) (l')
  结论: IsMinFilter f (l ⊓ l') a
  证明: h.filter_mono inf_le_left

Depends on / 依赖: filter_mono, h.filter_mono, inf_le_left
-/
theorem IsMinFilter.filter_inf (h : IsMinFilter f l a) (l') : IsMinFilter f (l ⊓ l') a :=
  h.filter_mono inf_le_left

/--
theorem `IsMaxFilter.filter_inf` / 定理 `IsMaxFilter.filter_inf`

English:
theorem IsMaxFilter.filter_inf
  given: (h : IsMaxFilter f l a) (l')
  statement: IsMaxFilter f (l ⊓ l') a
  proof: h.filter_mono inf_le_left

中文:
定理 IsMaxFilter.filter_inf
  条件: (h : IsMaxFilter f l a) (l')
  结论: IsMaxFilter f (l ⊓ l') a
  证明: h.filter_mono inf_le_left

Depends on / 依赖: filter_mono, h.filter_mono, inf_le_left
-/
theorem IsMaxFilter.filter_inf (h : IsMaxFilter f l a) (l') : IsMaxFilter f (l ⊓ l') a :=
  h.filter_mono inf_le_left

/--
theorem `IsExtrFilter.filter_inf` / 定理 `IsExtrFilter.filter_inf`

English:
theorem IsExtrFilter.filter_inf
  given: (h : IsExtrFilter f l a) (l')
  statement: IsExtrFilter f (l ⊓ l') a
  proof: h.filter_mono inf_le_left

中文:
定理 IsExtrFilter.filter_inf
  条件: (h : IsExtrFilter f l a) (l')
  结论: IsExtrFilter f (l ⊓ l') a
  证明: h.filter_mono inf_le_left

Depends on / 依赖: filter_mono, h.filter_mono, inf_le_left
-/
theorem IsExtrFilter.filter_inf (h : IsExtrFilter f l a) (l') : IsExtrFilter f (l ⊓ l') a :=
  h.filter_mono inf_le_left

/--
theorem `IsMinOn.on_subset` / 定理 `IsMinOn.on_subset`

English:
theorem IsMinOn.on_subset
  given: (hf : IsMinOn f t a) (h : s subseteq t)
  statement: IsMinOn f s a
  proof: hf.filter_mono principal_mono.2 h

中文:
定理 IsMinOn.on_subset
  条件: (hf : IsMinOn f t a) (h : s subseteq t)
  结论: IsMinOn f s a
  证明: hf.filter_mono principal_mono.2 h

Depends on / 依赖: filter_mono, hf.filter_mono, principal_mono
-/
theorem IsMinOn.on_subset (hf : IsMinOn f t a) (h : s subseteq t) : IsMinOn f s a :=
hf.filter_mono principal_mono.2 h

/--
theorem `IsMaxOn.on_subset` / 定理 `IsMaxOn.on_subset`

English:
theorem IsMaxOn.on_subset
  given: (hf : IsMaxOn f t a) (h : s subseteq t)
  statement: IsMaxOn f s a
  proof: hf.filter_mono principal_mono.2 h

中文:
定理 IsMaxOn.on_subset
  条件: (hf : IsMaxOn f t a) (h : s subseteq t)
  结论: IsMaxOn f s a
  证明: hf.filter_mono principal_mono.2 h

Depends on / 依赖: filter_mono, hf.filter_mono, principal_mono
-/
theorem IsMaxOn.on_subset (hf : IsMaxOn f t a) (h : s subseteq t) : IsMaxOn f s a :=
hf.filter_mono principal_mono.2 h

/--
theorem `IsExtrOn.on_subset` / 定理 `IsExtrOn.on_subset`

English:
theorem IsExtrOn.on_subset
  given: (hf : IsExtrOn f t a) (h : s subseteq t)
  statement: IsExtrOn f s a
  proof: hf.filter_mono principal_mono.2 h

中文:
定理 IsExtrOn.on_subset
  条件: (hf : IsExtrOn f t a) (h : s subseteq t)
  结论: IsExtrOn f s a
  证明: hf.filter_mono principal_mono.2 h

Depends on / 依赖: filter_mono, hf.filter_mono, principal_mono
-/
theorem IsExtrOn.on_subset (hf : IsExtrOn f t a) (h : s subseteq t) : IsExtrOn f s a :=
hf.filter_mono principal_mono.2 h

/--
theorem `IsMinOn.inter` / 定理 `IsMinOn.inter`

English:
theorem IsMinOn.inter
  given: (hf : IsMinOn f s a) (t)
  statement: IsMinOn f (s inter t) a
  proof: hf.on_subset inter_subset_left

中文:
定理 IsMinOn.inter
  条件: (hf : IsMinOn f s a) (t)
  结论: IsMinOn f (s inter t) a
  证明: hf.on_subset inter_subset_left

Depends on / 依赖: hf.on_subset, inter_subset_left, on_subset
-/
theorem IsMinOn.inter (hf : IsMinOn f s a) (t) : IsMinOn f (s inter t) a :=
  hf.on_subset inter_subset_left

/--
theorem `IsMaxOn.inter` / 定理 `IsMaxOn.inter`

English:
theorem IsMaxOn.inter
  given: (hf : IsMaxOn f s a) (t)
  statement: IsMaxOn f (s inter t) a
  proof: hf.on_subset inter_subset_left

中文:
定理 IsMaxOn.inter
  条件: (hf : IsMaxOn f s a) (t)
  结论: IsMaxOn f (s inter t) a
  证明: hf.on_subset inter_subset_left

Depends on / 依赖: hf.on_subset, inter_subset_left, on_subset
-/
theorem IsMaxOn.inter (hf : IsMaxOn f s a) (t) : IsMaxOn f (s inter t) a :=
  hf.on_subset inter_subset_left

/--
theorem `IsExtrOn.inter` / 定理 `IsExtrOn.inter`

English:
theorem IsExtrOn.inter
  given: (hf : IsExtrOn f s a) (t)
  statement: IsExtrOn f (s inter t) a
  proof: hf.on_subset inter_subset_left

中文:
定理 IsExtrOn.inter
  条件: (hf : IsExtrOn f s a) (t)
  结论: IsExtrOn f (s inter t) a
  证明: hf.on_subset inter_subset_left

Depends on / 依赖: hf.on_subset, inter_subset_left, on_subset
-/
theorem IsExtrOn.inter (hf : IsExtrOn f s a) (t) : IsExtrOn f (s inter t) a :=
  hf.on_subset inter_subset_left



/--
theorem `IsMinFilter.comp_mono` / 定理 `IsMinFilter.comp_mono`

English:
theorem IsMinFilter.comp_mono
  given: (hf : IsMinFilter f l a) {g : β -> γ} (hg : Monotone g)
  proof: mem_of_superset hf fun _x hx => hg hx

中文:
定理 IsMinFilter.comp_mono
  条件: (hf : IsMinFilter f l a) {g : β -> γ} (hg : Monotone g)
  证明: mem_of_superset hf fun _x hx => hg hx

Depends on / 依赖: mem_of_superset
-/
theorem IsMinFilter.comp_mono (hf : IsMinFilter f l a) {g : β -> γ} (hg : Monotone g) :
    IsMinFilter (g ∘ f) l a :=
  mem_of_superset hf fun _x hx => hg hx

/--
theorem `IsMaxFilter.comp_mono` / 定理 `IsMaxFilter.comp_mono`

English:
theorem IsMaxFilter.comp_mono
  given: (hf : IsMaxFilter f l a) {g : β -> γ} (hg : Monotone g)
  proof: mem_of_superset hf fun _x hx => hg hx

中文:
定理 IsMaxFilter.comp_mono
  条件: (hf : IsMaxFilter f l a) {g : β -> γ} (hg : Monotone g)
  证明: mem_of_superset hf fun _x hx => hg hx

Depends on / 依赖: mem_of_superset
-/
theorem IsMaxFilter.comp_mono (hf : IsMaxFilter f l a) {g : β -> γ} (hg : Monotone g) :
    IsMaxFilter (g ∘ f) l a :=
  mem_of_superset hf fun _x hx => hg hx

/--
theorem `IsExtrFilter.comp_mono` / 定理 `IsExtrFilter.comp_mono`

English:
theorem IsExtrFilter.comp_mono
  given: (hf : IsExtrFilter f l a) {g : β -> γ} (hg : Monotone g)
  proof: hf.elim (fun hf => (hf.comp_mono hg).isExtr) fun hf => (hf.comp_mono hg).isExtr

中文:
定理 IsExtrFilter.comp_mono
  条件: (hf : IsExtrFilter f l a) {g : β -> γ} (hg : Monotone g)
  证明: hf.elim (fun hf => (hf.comp_mono hg).isExtr) fun hf => (hf.comp_mono hg).isExtr

Depends on / 依赖: comp_mono, hf.comp_mono, hf.elim, isExtr
-/
theorem IsExtrFilter.comp_mono (hf : IsExtrFilter f l a) {g : β -> γ} (hg : Monotone g) :
    IsExtrFilter (g ∘ f) l a :=
  hf.elim (fun hf => (hf.comp_mono hg).isExtr) fun hf => (hf.comp_mono hg).isExtr

/--
theorem `IsMinFilter.comp_antitone` / 定理 `IsMinFilter.comp_antitone`

English:
theorem IsMinFilter.comp_antitone
  given: (hf : IsMinFilter f l a) {g : β -> γ} (hg : Antitone g)
  proof: hf.dual.comp_mono fun _ _ h => hg h

中文:
定理 IsMinFilter.comp_antitone
  条件: (hf : IsMinFilter f l a) {g : β -> γ} (hg : Antitone g)
  证明: hf.dual.comp_mono fun _ _ h => hg h

Depends on / 依赖: comp_mono, hf.dual.comp_mono
-/
theorem IsMinFilter.comp_antitone (hf : IsMinFilter f l a) {g : β -> γ} (hg : Antitone g) :
    IsMaxFilter (g ∘ f) l a :=
  hf.dual.comp_mono fun _ _ h => hg h

/--
theorem `IsMaxFilter.comp_antitone` / 定理 `IsMaxFilter.comp_antitone`

English:
theorem IsMaxFilter.comp_antitone
  given: (hf : IsMaxFilter f l a) {g : β -> γ} (hg : Antitone g)
  proof: hf.dual.comp_mono fun _ _ h => hg h

中文:
定理 IsMaxFilter.comp_antitone
  条件: (hf : IsMaxFilter f l a) {g : β -> γ} (hg : Antitone g)
  证明: hf.dual.comp_mono fun _ _ h => hg h

Depends on / 依赖: comp_mono, hf.dual.comp_mono
-/
theorem IsMaxFilter.comp_antitone (hf : IsMaxFilter f l a) {g : β -> γ} (hg : Antitone g) :
    IsMinFilter (g ∘ f) l a :=
  hf.dual.comp_mono fun _ _ h => hg h

/--
theorem `IsExtrFilter.comp_antitone` / 定理 `IsExtrFilter.comp_antitone`

English:
theorem IsExtrFilter.comp_antitone
  given: (hf : IsExtrFilter f l a) {g : β -> γ} (hg : Antitone g)
  proof: hf.dual.comp_mono fun _ _ h => hg h

中文:
定理 IsExtrFilter.comp_antitone
  条件: (hf : IsExtrFilter f l a) {g : β -> γ} (hg : Antitone g)
  证明: hf.dual.comp_mono fun _ _ h => hg h

Depends on / 依赖: comp_mono, hf.dual.comp_mono
-/
theorem IsExtrFilter.comp_antitone (hf : IsExtrFilter f l a) {g : β -> γ} (hg : Antitone g) :
    IsExtrFilter (g ∘ f) l a :=
  hf.dual.comp_mono fun _ _ h => hg h

/--
theorem `IsMinOn.comp_mono` / 定理 `IsMinOn.comp_mono`

English:
theorem IsMinOn.comp_mono
  given: (hf : IsMinOn f s a) {g : β -> γ} (hg : Monotone g)
  proof: IsMinFilter.comp_mono hf hg

中文:
定理 IsMinOn.comp_mono
  条件: (hf : IsMinOn f s a) {g : β -> γ} (hg : Monotone g)
  证明: IsMinFilter.comp_mono hf hg

Depends on / 依赖: IsMinFilter, IsMinFilter.comp_mono, comp_mono
-/
theorem IsMinOn.comp_mono (hf : IsMinOn f s a) {g : β -> γ} (hg : Monotone g) :
    IsMinOn (g ∘ f) s a :=
  IsMinFilter.comp_mono hf hg

/--
theorem `IsMaxOn.comp_mono` / 定理 `IsMaxOn.comp_mono`

English:
theorem IsMaxOn.comp_mono
  given: (hf : IsMaxOn f s a) {g : β -> γ} (hg : Monotone g)
  proof: IsMaxFilter.comp_mono hf hg

中文:
定理 IsMaxOn.comp_mono
  条件: (hf : IsMaxOn f s a) {g : β -> γ} (hg : Monotone g)
  证明: IsMaxFilter.comp_mono hf hg

Depends on / 依赖: IsMaxFilter, IsMaxFilter.comp_mono, comp_mono
-/
theorem IsMaxOn.comp_mono (hf : IsMaxOn f s a) {g : β -> γ} (hg : Monotone g) :
    IsMaxOn (g ∘ f) s a :=
  IsMaxFilter.comp_mono hf hg

/--
theorem `IsExtrOn.comp_mono` / 定理 `IsExtrOn.comp_mono`

English:
theorem IsExtrOn.comp_mono
  given: (hf : IsExtrOn f s a) {g : β -> γ} (hg : Monotone g)
  proof: IsExtrFilter.comp_mono hf hg

中文:
定理 IsExtrOn.comp_mono
  条件: (hf : IsExtrOn f s a) {g : β -> γ} (hg : Monotone g)
  证明: IsExtrFilter.comp_mono hf hg

Depends on / 依赖: IsExtrFilter, IsExtrFilter.comp_mono, comp_mono
-/
theorem IsExtrOn.comp_mono (hf : IsExtrOn f s a) {g : β -> γ} (hg : Monotone g) :
    IsExtrOn (g ∘ f) s a :=
  IsExtrFilter.comp_mono hf hg

/--
theorem `IsMinOn.comp_antitone` / 定理 `IsMinOn.comp_antitone`

English:
theorem IsMinOn.comp_antitone
  given: (hf : IsMinOn f s a) {g : β -> γ} (hg : Antitone g)
  proof: IsMinFilter.comp_antitone hf hg

中文:
定理 IsMinOn.comp_antitone
  条件: (hf : IsMinOn f s a) {g : β -> γ} (hg : Antitone g)
  证明: IsMinFilter.comp_antitone hf hg

Depends on / 依赖: IsMinFilter, IsMinFilter.comp_antitone, comp_antitone
-/
theorem IsMinOn.comp_antitone (hf : IsMinOn f s a) {g : β -> γ} (hg : Antitone g) :
    IsMaxOn (g ∘ f) s a :=
  IsMinFilter.comp_antitone hf hg

/--
theorem `IsMaxOn.comp_antitone` / 定理 `IsMaxOn.comp_antitone`

English:
theorem IsMaxOn.comp_antitone
  given: (hf : IsMaxOn f s a) {g : β -> γ} (hg : Antitone g)
  proof: IsMaxFilter.comp_antitone hf hg

中文:
定理 IsMaxOn.comp_antitone
  条件: (hf : IsMaxOn f s a) {g : β -> γ} (hg : Antitone g)
  证明: IsMaxFilter.comp_antitone hf hg

Depends on / 依赖: IsMaxFilter, IsMaxFilter.comp_antitone, comp_antitone
-/
theorem IsMaxOn.comp_antitone (hf : IsMaxOn f s a) {g : β -> γ} (hg : Antitone g) :
    IsMinOn (g ∘ f) s a :=
  IsMaxFilter.comp_antitone hf hg

/--
theorem `IsExtrOn.comp_antitone` / 定理 `IsExtrOn.comp_antitone`

English:
theorem IsExtrOn.comp_antitone
  given: (hf : IsExtrOn f s a) {g : β -> γ} (hg : Antitone g)
  proof: IsExtrFilter.comp_antitone hf hg

中文:
定理 IsExtrOn.comp_antitone
  条件: (hf : IsExtrOn f s a) {g : β -> γ} (hg : Antitone g)
  证明: IsExtrFilter.comp_antitone hf hg

Depends on / 依赖: IsExtrFilter, IsExtrFilter.comp_antitone, comp_antitone
-/
theorem IsExtrOn.comp_antitone (hf : IsExtrOn f s a) {g : β -> γ} (hg : Antitone g) :
    IsExtrOn (g ∘ f) s a :=
  IsExtrFilter.comp_antitone hf hg

/--
theorem `IsMinFilter.bicomp_mono` / 定理 `IsMinFilter.bicomp_mono`

English:
theorem IsMinFilter.bicomp_mono
  statement: [Preorder δ] {op : β -> γ -> δ}
  proof: mem_of_superset (inter_mem hf hg) fun _x ⟨hfx, hgx⟩ => hop hfx hgx

中文:
定理 IsMinFilter.bicomp_mono
  结论: [Preorder δ] {op : β -> γ -> δ}
  证明: mem_of_superset (inter_mem hf hg) fun _x ⟨hfx, hgx⟩ => hop hfx hgx

Depends on / 依赖: inter_mem, mem_of_superset
-/
theorem IsMinFilter.bicomp_mono [Preorder δ] {op : β -> γ -> δ}
    (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMinFilter f l a) {g : α -> γ}
    (hg : IsMinFilter g l a) : IsMinFilter (fun x => op (f x) (g x)) l a :=
  mem_of_superset (inter_mem hf hg) fun _x ⟨hfx, hgx⟩ => hop hfx hgx

/--
theorem `IsMaxFilter.bicomp_mono` / 定理 `IsMaxFilter.bicomp_mono`

English:
theorem IsMaxFilter.bicomp_mono
  statement: [Preorder δ] {op : β -> γ -> δ}
  proof: mem_of_superset (inter_mem hf hg) fun _x ⟨hfx, hgx⟩ => hop hfx hgx

中文:
定理 IsMaxFilter.bicomp_mono
  结论: [Preorder δ] {op : β -> γ -> δ}
  证明: mem_of_superset (inter_mem hf hg) fun _x ⟨hfx, hgx⟩ => hop hfx hgx

Depends on / 依赖: inter_mem, mem_of_superset
-/
theorem IsMaxFilter.bicomp_mono [Preorder δ] {op : β -> γ -> δ}
    (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMaxFilter f l a) {g : α -> γ}
    (hg : IsMaxFilter g l a) : IsMaxFilter (fun x => op (f x) (g x)) l a :=
  mem_of_superset (inter_mem hf hg) fun _x ⟨hfx, hgx⟩ => hop hfx hgx

-- No `Extr` version because we need `hf` and `hg` to be of the same kind
/--
theorem `IsMinOn.bicomp_mono` / 定理 `IsMinOn.bicomp_mono`

English:
theorem IsMinOn.bicomp_mono
  statement: [Preorder δ] {op : β -> γ -> δ}
  proof: IsMinFilter.bicomp_mono hop hf hg

中文:
定理 IsMinOn.bicomp_mono
  结论: [Preorder δ] {op : β -> γ -> δ}
  证明: IsMinFilter.bicomp_mono hop hf hg

Depends on / 依赖: IsMinFilter, IsMinFilter.bicomp_mono, bicomp_mono
-/
theorem IsMinOn.bicomp_mono [Preorder δ] {op : β -> γ -> δ}
    (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMinOn f s a) {g : α -> γ}
    (hg : IsMinOn g s a) : IsMinOn (fun x => op (f x) (g x)) s a :=
  IsMinFilter.bicomp_mono hop hf hg

/--
theorem `IsMaxOn.bicomp_mono` / 定理 `IsMaxOn.bicomp_mono`

English:
theorem IsMaxOn.bicomp_mono
  statement: [Preorder δ] {op : β -> γ -> δ}
  proof: IsMaxFilter.bicomp_mono hop hf hg

中文:
定理 IsMaxOn.bicomp_mono
  结论: [Preorder δ] {op : β -> γ -> δ}
  证明: IsMaxFilter.bicomp_mono hop hf hg

Depends on / 依赖: IsMaxFilter, IsMaxFilter.bicomp_mono, bicomp_mono
-/
theorem IsMaxOn.bicomp_mono [Preorder δ] {op : β -> γ -> δ}
    (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMaxOn f s a) {g : α -> γ}
    (hg : IsMaxOn g s a) : IsMaxOn (fun x => op (f x) (g x)) s a :=
  IsMaxFilter.bicomp_mono hop hf hg



/--
theorem `IsMinFilter.comp_tendsto` / 定理 `IsMinFilter.comp_tendsto`

English:
theorem IsMinFilter.comp_tendsto
  statement: {g : δ -> α} {l' : Filter δ} {b : δ} (hf : IsMinFilter f l (g b))
  proof: hg hf

中文:
定理 IsMinFilter.comp_tendsto
  结论: {g : δ -> α} {l' : Filter δ} {b : δ} (hf : IsMinFilter f l (g b))
  证明: hg hf
-/
theorem IsMinFilter.comp_tendsto {g : δ -> α} {l' : Filter δ} {b : δ} (hf : IsMinFilter f l (g b))
    (hg : Tendsto g l' l) : IsMinFilter (f ∘ g) l' b :=
  hg hf

/--
theorem `IsMaxFilter.comp_tendsto` / 定理 `IsMaxFilter.comp_tendsto`

English:
theorem IsMaxFilter.comp_tendsto
  statement: {g : δ -> α} {l' : Filter δ} {b : δ} (hf : IsMaxFilter f l (g b))
  proof: hg hf

中文:
定理 IsMaxFilter.comp_tendsto
  结论: {g : δ -> α} {l' : Filter δ} {b : δ} (hf : IsMaxFilter f l (g b))
  证明: hg hf
-/
theorem IsMaxFilter.comp_tendsto {g : δ -> α} {l' : Filter δ} {b : δ} (hf : IsMaxFilter f l (g b))
    (hg : Tendsto g l' l) : IsMaxFilter (f ∘ g) l' b :=
  hg hf

/--
theorem `IsExtrFilter.comp_tendsto` / 定理 `IsExtrFilter.comp_tendsto`

English:
theorem IsExtrFilter.comp_tendsto
  statement: {g : δ -> α} {l' : Filter δ} {b : δ} (hf : IsExtrFilter f l (g b))
  proof: hf.elim (fun hf => (hf.comp_tendsto hg).isExtr) fun hf => (hf.comp_tendsto hg).isExtr

中文:
定理 IsExtrFilter.comp_tendsto
  结论: {g : δ -> α} {l' : Filter δ} {b : δ} (hf : IsExtrFilter f l (g b))
  证明: hf.elim (fun hf => (hf.comp_tendsto hg).isExtr) fun hf => (hf.comp_tendsto hg).isExtr

Depends on / 依赖: comp_tendsto, hf.comp_tendsto, hf.elim, isExtr
-/
theorem IsExtrFilter.comp_tendsto {g : δ -> α} {l' : Filter δ} {b : δ} (hf : IsExtrFilter f l (g b))
    (hg : Tendsto g l' l) : IsExtrFilter (f ∘ g) l' b :=
  hf.elim (fun hf => (hf.comp_tendsto hg).isExtr) fun hf => (hf.comp_tendsto hg).isExtr

/--
theorem `IsMinOn.on_preimage` / 定理 `IsMinOn.on_preimage`

English:
theorem IsMinOn.on_preimage
  given: (g : δ -> α) {b : δ} (hf : IsMinOn f s (g b))
  proof: hf.comp_tendsto (tendsto_principal_principal.mpr <| Subset.refl _)

中文:
定理 IsMinOn.on_preimage
  条件: (g : δ -> α) {b : δ} (hf : IsMinOn f s (g b))
  证明: hf.comp_tendsto (tendsto_principal_principal.mpr <| Subset.refl _)

Depends on / 依赖: Subset, Subset.refl, comp_tendsto, hf.comp_tendsto, tendsto_principal_principal, tendsto_principal_principal.mpr
-/
theorem IsMinOn.on_preimage (g : δ -> α) {b : δ} (hf : IsMinOn f s (g b)) :
    IsMinOn (f ∘ g) (g ⁻¹' s) b :=
  hf.comp_tendsto (tendsto_principal_principal.mpr <| Subset.refl _)

/--
theorem `IsMaxOn.on_preimage` / 定理 `IsMaxOn.on_preimage`

English:
theorem IsMaxOn.on_preimage
  given: (g : δ -> α) {b : δ} (hf : IsMaxOn f s (g b))
  proof: hf.comp_tendsto (tendsto_principal_principal.mpr <| Subset.refl _)

中文:
定理 IsMaxOn.on_preimage
  条件: (g : δ -> α) {b : δ} (hf : IsMaxOn f s (g b))
  证明: hf.comp_tendsto (tendsto_principal_principal.mpr <| Subset.refl _)

Depends on / 依赖: Subset, Subset.refl, comp_tendsto, hf.comp_tendsto, tendsto_principal_principal, tendsto_principal_principal.mpr
-/
theorem IsMaxOn.on_preimage (g : δ -> α) {b : δ} (hf : IsMaxOn f s (g b)) :
    IsMaxOn (f ∘ g) (g ⁻¹' s) b :=
  hf.comp_tendsto (tendsto_principal_principal.mpr <| Subset.refl _)

/--
theorem `IsExtrOn.on_preimage` / 定理 `IsExtrOn.on_preimage`

English:
theorem IsExtrOn.on_preimage
  given: (g : δ -> α) {b : δ} (hf : IsExtrOn f s (g b))
  proof: hf.elim (fun hf => (hf.on_preimage g).isExtr) fun hf => (hf.on_preimage g).isExtr

中文:
定理 IsExtrOn.on_preimage
  条件: (g : δ -> α) {b : δ} (hf : IsExtrOn f s (g b))
  证明: hf.elim (fun hf => (hf.on_preimage g).isExtr) fun hf => (hf.on_preimage g).isExtr

Depends on / 依赖: hf.elim, hf.on_preimage, isExtr, on_preimage
-/
theorem IsExtrOn.on_preimage (g : δ -> α) {b : δ} (hf : IsExtrOn f s (g b)) :
    IsExtrOn (f ∘ g) (g ⁻¹' s) b :=
  hf.elim (fun hf => (hf.on_preimage g).isExtr) fun hf => (hf.on_preimage g).isExtr

/--
theorem `IsMinOn.comp_mapsTo` / 定理 `IsMinOn.comp_mapsTo`

English:
theorem IsMinOn.comp_mapsTo
  statement: {t : Set δ} {g : δ -> α} {b : δ} (hf : IsMinOn f s a) (hg : MapsTo g t s)
  proof: fun y hy => by
  simpa only [ha, (· ∘ ·)] using! hf (hg hy)

中文:
定理 IsMinOn.comp_mapsTo
  结论: {t : Set δ} {g : δ -> α} {b : δ} (hf : IsMinOn f s a) (hg : MapsTo g t s)
  证明: fun y hy => by
  simpa only [ha, (· ∘ ·)] using! hf (hg hy)
-/
theorem IsMinOn.comp_mapsTo {t : Set δ} {g : δ -> α} {b : δ} (hf : IsMinOn f s a) (hg : MapsTo g t s)
    (ha : g b = a) : IsMinOn (f ∘ g) t b := fun y hy => by
  simpa only [ha, (· ∘ ·)] using! hf (hg hy)

/--
theorem `IsMaxOn.comp_mapsTo` / 定理 `IsMaxOn.comp_mapsTo`

English:
theorem IsMaxOn.comp_mapsTo
  statement: {t : Set δ} {g : δ -> α} {b : δ} (hf : IsMaxOn f s a) (hg : MapsTo g t s)
  proof: hf.dual.comp_mapsTo hg ha

中文:
定理 IsMaxOn.comp_mapsTo
  结论: {t : Set δ} {g : δ -> α} {b : δ} (hf : IsMaxOn f s a) (hg : MapsTo g t s)
  证明: hf.dual.comp_mapsTo hg ha

Depends on / 依赖: comp_mapsTo, hf.dual.comp_mapsTo
-/
theorem IsMaxOn.comp_mapsTo {t : Set δ} {g : δ -> α} {b : δ} (hf : IsMaxOn f s a) (hg : MapsTo g t s)
    (ha : g b = a) : IsMaxOn (f ∘ g) t b :=
  hf.dual.comp_mapsTo hg ha

/--
theorem `IsExtrOn.comp_mapsTo` / 定理 `IsExtrOn.comp_mapsTo`

English:
theorem IsExtrOn.comp_mapsTo
  statement: {t : Set δ} {g : δ -> α} {b : δ} (hf : IsExtrOn f s a)
  proof: hf.elim (fun h => Or.inl <| h.comp_mapsTo hg ha) fun h => Or.inr h.comp_mapsTo hg ha

中文:
定理 IsExtrOn.comp_mapsTo
  结论: {t : Set δ} {g : δ -> α} {b : δ} (hf : IsExtrOn f s a)
  证明: hf.elim (fun h => Or.inl <| h.comp_mapsTo hg ha) fun h => Or.inr h.comp_mapsTo hg ha

Depends on / 依赖: Or.inl, Or.inr, comp_mapsTo, h.comp_mapsTo, hf.elim
-/
theorem IsExtrOn.comp_mapsTo {t : Set δ} {g : δ -> α} {b : δ} (hf : IsExtrOn f s a)
    (hg : MapsTo g t s) (ha : g b = a) : IsExtrOn (f ∘ g) t b :=
hf.elim (fun h => Or.inl <| h.comp_mapsTo hg ha) fun h => Or.inr h.comp_mapsTo hg ha

end Preorder

/-! ### Pointwise addition -/


section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
  {f g : α -> β} {a : α} {s : Set α} {l : Filter α}

/--
theorem `IsMinFilter.add` / 定理 `IsMinFilter.add`

English:
theorem IsMinFilter.add
  given: (hf : IsMinFilter f l a) (hg : IsMinFilter g l a)
  proof: show IsMinFilter (fun x => f x + g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => add_le_add hx hy) hg

中文:
定理 IsMinFilter.add
  条件: (hf : IsMinFilter f l a) (hg : IsMinFilter g l a)
  证明: show IsMinFilter (fun x => f x + g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => add_le_add hx hy) hg

Depends on / 依赖: IsMinFilter, add_le_add, bicomp_mono, hf.bicomp_mono
-/
theorem IsMinFilter.add (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => f x + g x) l a :=
  show IsMinFilter (fun x => f x + g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => add_le_add hx hy) hg

/--
theorem `IsMaxFilter.add` / 定理 `IsMaxFilter.add`

English:
theorem IsMaxFilter.add
  given: (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a)
  proof: show IsMaxFilter (fun x => f x + g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => add_le_add hx hy) hg

中文:
定理 IsMaxFilter.add
  条件: (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a)
  证明: show IsMaxFilter (fun x => f x + g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => add_le_add hx hy) hg

Depends on / 依赖: IsMaxFilter, add_le_add, bicomp_mono, hf.bicomp_mono
-/
theorem IsMaxFilter.add (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => f x + g x) l a :=
  show IsMaxFilter (fun x => f x + g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => add_le_add hx hy) hg

/--
theorem `IsMinOn.add` / 定理 `IsMinOn.add`

English:
theorem IsMinOn.add
  given: (hf : IsMinOn f s a) (hg : IsMinOn g s a)
  statement: IsMinOn (fun x => f x + g x) s a
  proof: IsMinFilter.add hf hg

中文:
定理 IsMinOn.add
  条件: (hf : IsMinOn f s a) (hg : IsMinOn g s a)
  结论: IsMinOn (fun x => f x + g x) s a
  证明: IsMinFilter.add hf hg

Depends on / 依赖: IsMinFilter, IsMinFilter.add
-/
theorem IsMinOn.add (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => f x + g x) s a :=
  IsMinFilter.add hf hg

/--
theorem `IsMaxOn.add` / 定理 `IsMaxOn.add`

English:
theorem IsMaxOn.add
  given: (hf : IsMaxOn f s a) (hg : IsMaxOn g s a)
  statement: IsMaxOn (fun x => f x + g x) s a
  proof: IsMaxFilter.add hf hg

中文:
定理 IsMaxOn.add
  条件: (hf : IsMaxOn f s a) (hg : IsMaxOn g s a)
  结论: IsMaxOn (fun x => f x + g x) s a
  证明: IsMaxFilter.add hf hg

Depends on / 依赖: IsMaxFilter, IsMaxFilter.add
-/
theorem IsMaxOn.add (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => f x + g x) s a :=
  IsMaxFilter.add hf hg

end OrderedAddCommMonoid

/-! ### Pointwise negation and subtraction -/


section OrderedAddCommGroup

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  {f g : α -> β} {a : α} {s : Set α} {l : Filter α}

/--
theorem `IsMinFilter.neg` / 定理 `IsMinFilter.neg`

English:
theorem IsMinFilter.neg
  given: (hf : IsMinFilter f l a)
  statement: IsMaxFilter (fun x => -f x) l a
  proof: hf.comp_antitone fun _x _y hx => neg_le_neg hx

中文:
定理 IsMinFilter.neg
  条件: (hf : IsMinFilter f l a)
  结论: IsMaxFilter (fun x => -f x) l a
  证明: hf.comp_antitone fun _x _y hx => neg_le_neg hx

Depends on / 依赖: comp_antitone, hf.comp_antitone, neg_le_neg
-/
theorem IsMinFilter.neg (hf : IsMinFilter f l a) : IsMaxFilter (fun x => -f x) l a :=
  hf.comp_antitone fun _x _y hx => neg_le_neg hx

/--
theorem `IsMaxFilter.neg` / 定理 `IsMaxFilter.neg`

English:
theorem IsMaxFilter.neg
  given: (hf : IsMaxFilter f l a)
  statement: IsMinFilter (fun x => -f x) l a
  proof: hf.comp_antitone fun _x _y hx => neg_le_neg hx

中文:
定理 IsMaxFilter.neg
  条件: (hf : IsMaxFilter f l a)
  结论: IsMinFilter (fun x => -f x) l a
  证明: hf.comp_antitone fun _x _y hx => neg_le_neg hx

Depends on / 依赖: comp_antitone, hf.comp_antitone, neg_le_neg
-/
theorem IsMaxFilter.neg (hf : IsMaxFilter f l a) : IsMinFilter (fun x => -f x) l a :=
  hf.comp_antitone fun _x _y hx => neg_le_neg hx

/--
theorem `IsExtrFilter.neg` / 定理 `IsExtrFilter.neg`

English:
theorem IsExtrFilter.neg
  given: (hf : IsExtrFilter f l a)
  statement: IsExtrFilter (fun x => -f x) l a
  proof: hf.elim (fun hf => hf.neg.isExtr) fun hf => hf.neg.isExtr

中文:
定理 IsExtrFilter.neg
  条件: (hf : IsExtrFilter f l a)
  结论: IsExtrFilter (fun x => -f x) l a
  证明: hf.elim (fun hf => hf.neg.isExtr) fun hf => hf.neg.isExtr

Depends on / 依赖: hf.elim, hf.neg.isExtr, isExtr
-/
theorem IsExtrFilter.neg (hf : IsExtrFilter f l a) : IsExtrFilter (fun x => -f x) l a :=
  hf.elim (fun hf => hf.neg.isExtr) fun hf => hf.neg.isExtr

/--
theorem `IsMinOn.neg` / 定理 `IsMinOn.neg`

English:
theorem IsMinOn.neg
  given: (hf : IsMinOn f s a)
  statement: IsMaxOn (fun x => -f x) s a
  proof: hf.comp_antitone fun _x _y hx => neg_le_neg hx

中文:
定理 IsMinOn.neg
  条件: (hf : IsMinOn f s a)
  结论: IsMaxOn (fun x => -f x) s a
  证明: hf.comp_antitone fun _x _y hx => neg_le_neg hx

Depends on / 依赖: comp_antitone, hf.comp_antitone, neg_le_neg
-/
theorem IsMinOn.neg (hf : IsMinOn f s a) : IsMaxOn (fun x => -f x) s a :=
  hf.comp_antitone fun _x _y hx => neg_le_neg hx

/--
theorem `IsMaxOn.neg` / 定理 `IsMaxOn.neg`

English:
theorem IsMaxOn.neg
  given: (hf : IsMaxOn f s a)
  statement: IsMinOn (fun x => -f x) s a
  proof: hf.comp_antitone fun _x _y hx => neg_le_neg hx

中文:
定理 IsMaxOn.neg
  条件: (hf : IsMaxOn f s a)
  结论: IsMinOn (fun x => -f x) s a
  证明: hf.comp_antitone fun _x _y hx => neg_le_neg hx

Depends on / 依赖: comp_antitone, hf.comp_antitone, neg_le_neg
-/
theorem IsMaxOn.neg (hf : IsMaxOn f s a) : IsMinOn (fun x => -f x) s a :=
  hf.comp_antitone fun _x _y hx => neg_le_neg hx

/--
theorem `IsExtrOn.neg` / 定理 `IsExtrOn.neg`

English:
theorem IsExtrOn.neg
  given: (hf : IsExtrOn f s a)
  statement: IsExtrOn (fun x => -f x) s a
  proof: hf.elim (fun hf => hf.neg.isExtr) fun hf => hf.neg.isExtr

中文:
定理 IsExtrOn.neg
  条件: (hf : IsExtrOn f s a)
  结论: IsExtrOn (fun x => -f x) s a
  证明: hf.elim (fun hf => hf.neg.isExtr) fun hf => hf.neg.isExtr

Depends on / 依赖: hf.elim, hf.neg.isExtr, isExtr
-/
theorem IsExtrOn.neg (hf : IsExtrOn f s a) : IsExtrOn (fun x => -f x) s a :=
  hf.elim (fun hf => hf.neg.isExtr) fun hf => hf.neg.isExtr

/--
theorem `IsMinFilter.sub` / 定理 `IsMinFilter.sub`

English:
theorem IsMinFilter.sub
  given: (hf : IsMinFilter f l a) (hg : IsMaxFilter g l a)
  proof: by simpa only [sub_eq_add_neg] using hf.add hg.neg

中文:
定理 IsMinFilter.sub
  条件: (hf : IsMinFilter f l a) (hg : IsMaxFilter g l a)
  证明: by simpa only [sub_eq_add_neg] using hf.add hg.neg

Depends on / 依赖: IsAdicComplete, Subsingleton, hf.add, hg.neg, of_subsingleton, sub_eq_add_neg
-/
theorem IsMinFilter.sub (hf : IsMinFilter f l a) (hg : IsMaxFilter g l a) :
    IsMinFilter (fun x => f x - g x) l a := by simpa only [sub_eq_add_neg] using hf.add hg.neg

/--
theorem `IsMaxFilter.sub` / 定理 `IsMaxFilter.sub`

English:
theorem IsMaxFilter.sub
  given: (hf : IsMaxFilter f l a) (hg : IsMinFilter g l a)
  proof: by simpa only [sub_eq_add_neg] using hf.add hg.neg

中文:
定理 IsMaxFilter.sub
  条件: (hf : IsMaxFilter f l a) (hg : IsMinFilter g l a)
  证明: by simpa only [sub_eq_add_neg] using hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem IsMaxFilter.sub (hf : IsMaxFilter f l a) (hg : IsMinFilter g l a) :
    IsMaxFilter (fun x => f x - g x) l a := by simpa only [sub_eq_add_neg] using hf.add hg.neg

/--
theorem `IsMinOn.sub` / 定理 `IsMinOn.sub`

English:
theorem IsMinOn.sub
  given: (hf : IsMinOn f s a) (hg : IsMaxOn g s a)
  proof: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

中文:
定理 IsMinOn.sub
  条件: (hf : IsMinOn f s a) (hg : IsMaxOn g s a)
  证明: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem IsMinOn.sub (hf : IsMinOn f s a) (hg : IsMaxOn g s a) :
    IsMinOn (fun x => f x - g x) s a := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/--
theorem `IsMaxOn.sub` / 定理 `IsMaxOn.sub`

English:
theorem IsMaxOn.sub
  given: (hf : IsMaxOn f s a) (hg : IsMinOn g s a)
  proof: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

中文:
定理 IsMaxOn.sub
  条件: (hf : IsMaxOn f s a) (hg : IsMinOn g s a)
  证明: by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem IsMaxOn.sub (hf : IsMaxOn f s a) (hg : IsMinOn g s a) :
    IsMaxOn (fun x => f x - g x) s a := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end OrderedAddCommGroup

/-! ### Pointwise `sup`/`inf` -/


section SemilatticeSup

variable [SemilatticeSup β] {f g : α -> β} {a : α} {s : Set α} {l : Filter α}

/--
theorem `IsMinFilter.sup` / 定理 `IsMinFilter.sup`

English:
theorem IsMinFilter.sup
  given: (hf : IsMinFilter f l a) (hg : IsMinFilter g l a)
  proof: show IsMinFilter (fun x => f x ⊔ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => sup_le_sup hx hy) hg

中文:
定理 IsMinFilter.sup
  条件: (hf : IsMinFilter f l a) (hg : IsMinFilter g l a)
  证明: show IsMinFilter (fun x => f x ⊔ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => sup_le_sup hx hy) hg

Depends on / 依赖: IsMinFilter, bicomp_mono, hf.bicomp_mono, sup_le_sup
-/
theorem IsMinFilter.sup (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => f x ⊔ g x) l a :=
  show IsMinFilter (fun x => f x ⊔ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => sup_le_sup hx hy) hg

/--
theorem `IsMaxFilter.sup` / 定理 `IsMaxFilter.sup`

English:
theorem IsMaxFilter.sup
  given: (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a)
  proof: show IsMaxFilter (fun x => f x ⊔ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => sup_le_sup hx hy) hg

中文:
定理 IsMaxFilter.sup
  条件: (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a)
  证明: show IsMaxFilter (fun x => f x ⊔ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => sup_le_sup hx hy) hg

Depends on / 依赖: IsMaxFilter, bicomp_mono, hf.bicomp_mono, sup_le_sup
-/
theorem IsMaxFilter.sup (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => f x ⊔ g x) l a :=
  show IsMaxFilter (fun x => f x ⊔ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => sup_le_sup hx hy) hg

/--
theorem `IsMinOn.sup` / 定理 `IsMinOn.sup`

English:
theorem IsMinOn.sup
  given: (hf : IsMinOn f s a) (hg : IsMinOn g s a)
  statement: IsMinOn (fun x => f x ⊔ g x) s a
  proof: IsMinFilter.sup hf hg

中文:
定理 IsMinOn.sup
  条件: (hf : IsMinOn f s a) (hg : IsMinOn g s a)
  结论: IsMinOn (fun x => f x ⊔ g x) s a
  证明: IsMinFilter.sup hf hg

Depends on / 依赖: IsMinFilter, IsMinFilter.sup
-/
theorem IsMinOn.sup (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => f x ⊔ g x) s a :=
  IsMinFilter.sup hf hg

/--
theorem `IsMaxOn.sup` / 定理 `IsMaxOn.sup`

English:
theorem IsMaxOn.sup
  given: (hf : IsMaxOn f s a) (hg : IsMaxOn g s a)
  statement: IsMaxOn (fun x => f x ⊔ g x) s a
  proof: IsMaxFilter.sup hf hg

中文:
定理 IsMaxOn.sup
  条件: (hf : IsMaxOn f s a) (hg : IsMaxOn g s a)
  结论: IsMaxOn (fun x => f x ⊔ g x) s a
  证明: IsMaxFilter.sup hf hg

Depends on / 依赖: IsMaxFilter, IsMaxFilter.sup
-/
theorem IsMaxOn.sup (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => f x ⊔ g x) s a :=
  IsMaxFilter.sup hf hg

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf β] {f g : α -> β} {a : α} {s : Set α} {l : Filter α}

/--
theorem `IsMinFilter.inf` / 定理 `IsMinFilter.inf`

English:
theorem IsMinFilter.inf
  given: (hf : IsMinFilter f l a) (hg : IsMinFilter g l a)
  proof: show IsMinFilter (fun x => f x ⊓ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => inf_le_inf hx hy) hg

中文:
定理 IsMinFilter.inf
  条件: (hf : IsMinFilter f l a) (hg : IsMinFilter g l a)
  证明: show IsMinFilter (fun x => f x ⊓ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => inf_le_inf hx hy) hg

Depends on / 依赖: IsMinFilter, bicomp_mono, hf.bicomp_mono, inf_le_inf
-/
theorem IsMinFilter.inf (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => f x ⊓ g x) l a :=
  show IsMinFilter (fun x => f x ⊓ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => inf_le_inf hx hy) hg

/--
theorem `IsMaxFilter.inf` / 定理 `IsMaxFilter.inf`

English:
theorem IsMaxFilter.inf
  given: (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a)
  proof: show IsMaxFilter (fun x => f x ⊓ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => inf_le_inf hx hy) hg

中文:
定理 IsMaxFilter.inf
  条件: (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a)
  证明: show IsMaxFilter (fun x => f x ⊓ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => inf_le_inf hx hy) hg

Depends on / 依赖: IsMaxFilter, bicomp_mono, hf.bicomp_mono, inf_le_inf
-/
theorem IsMaxFilter.inf (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => f x ⊓ g x) l a :=
  show IsMaxFilter (fun x => f x ⊓ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => inf_le_inf hx hy) hg

/--
theorem `IsMinOn.inf` / 定理 `IsMinOn.inf`

English:
theorem IsMinOn.inf
  given: (hf : IsMinOn f s a) (hg : IsMinOn g s a)
  statement: IsMinOn (fun x => f x ⊓ g x) s a
  proof: IsMinFilter.inf hf hg

中文:
定理 IsMinOn.inf
  条件: (hf : IsMinOn f s a) (hg : IsMinOn g s a)
  结论: IsMinOn (fun x => f x ⊓ g x) s a
  证明: IsMinFilter.inf hf hg

Depends on / 依赖: IsMinFilter, IsMinFilter.inf
-/
theorem IsMinOn.inf (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => f x ⊓ g x) s a :=
  IsMinFilter.inf hf hg

/--
theorem `IsMaxOn.inf` / 定理 `IsMaxOn.inf`

English:
theorem IsMaxOn.inf
  given: (hf : IsMaxOn f s a) (hg : IsMaxOn g s a)
  statement: IsMaxOn (fun x => f x ⊓ g x) s a
  proof: IsMaxFilter.inf hf hg

中文:
定理 IsMaxOn.inf
  条件: (hf : IsMaxOn f s a) (hg : IsMaxOn g s a)
  结论: IsMaxOn (fun x => f x ⊓ g x) s a
  证明: IsMaxFilter.inf hf hg

Depends on / 依赖: IsMaxFilter, IsMaxFilter.inf
-/
theorem IsMaxOn.inf (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => f x ⊓ g x) s a :=
  IsMaxFilter.inf hf hg

end SemilatticeInf

/-! ### Pointwise `min`/`max` -/


section LinearOrder

variable [LinearOrder β] {f g : α -> β} {a : α} {s : Set α} {l : Filter α}

/--
theorem `IsMinFilter.min` / 定理 `IsMinFilter.min`

English:
theorem IsMinFilter.min
  given: (hf : IsMinFilter f l a) (hg : IsMinFilter g l a)
  proof: show IsMinFilter (fun x => Min.min (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => min_le_min hx hy) hg

中文:
定理 IsMinFilter.min
  条件: (hf : IsMinFilter f l a) (hg : IsMinFilter g l a)
  证明: show IsMinFilter (fun x => Min.min (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => min_le_min hx hy) hg

Depends on / 依赖: IsMinFilter, Min.min, bicomp_mono, hf.bicomp_mono, min_le_min
-/
theorem IsMinFilter.min (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => min (f x) (g x)) l a :=
  show IsMinFilter (fun x => Min.min (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => min_le_min hx hy) hg

/--
theorem `IsMaxFilter.min` / 定理 `IsMaxFilter.min`

English:
theorem IsMaxFilter.min
  given: (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a)
  proof: show IsMaxFilter (fun x => Min.min (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => min_le_min hx hy) hg

中文:
定理 IsMaxFilter.min
  条件: (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a)
  证明: show IsMaxFilter (fun x => Min.min (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => min_le_min hx hy) hg

Depends on / 依赖: AdicCompletion, AdicCompletion.algebraMap_apply, AdicCompletion.isAdicComplete, Ideal.map, Ideal.map_span, Ideal.span, IsAdicComplete, IsAdicComplete.congr_ringEquiv, IsAdicComplete.map_algebraMap_iff, IsMaxFilter, Min.min, MvPolynomial, MvPolynomial.coe_X, MvPolynomial.idealOfVars, MvPolynomial.idealOfVars_fg, Set.range, Set.range_comp, algebraMap, algebraMap_apply, bicomp_mono
-/
theorem IsMaxFilter.min (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => min (f x) (g x)) l a :=
  show IsMaxFilter (fun x => Min.min (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => min_le_min hx hy) hg

/--
theorem `IsMinOn.min` / 定理 `IsMinOn.min`

English:
theorem IsMinOn.min
  given: (hf : IsMinOn f s a) (hg : IsMinOn g s a)
  proof: IsMinFilter.min hf hg

中文:
定理 IsMinOn.min
  条件: (hf : IsMinOn f s a) (hg : IsMinOn g s a)
  证明: IsMinFilter.min hf hg

Depends on / 依赖: IsMinFilter, IsMinFilter.min
-/
theorem IsMinOn.min (hf : IsMinOn f s a) (hg : IsMinOn g s a) :
    IsMinOn (fun x => min (f x) (g x)) s a :=
  IsMinFilter.min hf hg

/--
theorem `IsMaxOn.min` / 定理 `IsMaxOn.min`

English:
theorem IsMaxOn.min
  given: (hf : IsMaxOn f s a) (hg : IsMaxOn g s a)
  proof: IsMaxFilter.min hf hg

中文:
定理 IsMaxOn.min
  条件: (hf : IsMaxOn f s a) (hg : IsMaxOn g s a)
  证明: IsMaxFilter.min hf hg

Depends on / 依赖: IsMaxFilter, IsMaxFilter.min
-/
theorem IsMaxOn.min (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) :
    IsMaxOn (fun x => min (f x) (g x)) s a :=
  IsMaxFilter.min hf hg

/--
theorem `IsMinFilter.max` / 定理 `IsMinFilter.max`

English:
theorem IsMinFilter.max
  given: (hf : IsMinFilter f l a) (hg : IsMinFilter g l a)
  proof: show IsMinFilter (fun x => Max.max (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => max_le_max hx hy) hg

中文:
定理 IsMinFilter.max
  条件: (hf : IsMinFilter f l a) (hg : IsMinFilter g l a)
  证明: show IsMinFilter (fun x => Max.max (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => max_le_max hx hy) hg

Depends on / 依赖: IsMinFilter, Max.max, bicomp_mono, hf.bicomp_mono, max_le_max
-/
theorem IsMinFilter.max (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => max (f x) (g x)) l a :=
  show IsMinFilter (fun x => Max.max (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => max_le_max hx hy) hg

/--
theorem `IsMaxFilter.max` / 定理 `IsMaxFilter.max`

English:
theorem IsMaxFilter.max
  given: (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a)
  proof: show IsMaxFilter (fun x => Max.max (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => max_le_max hx hy) hg

中文:
定理 IsMaxFilter.max
  条件: (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a)
  证明: show IsMaxFilter (fun x => Max.max (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => max_le_max hx hy) hg

Depends on / 依赖: IsMaxFilter, Max.max, bicomp_mono, hf.bicomp_mono, max_le_max
-/
theorem IsMaxFilter.max (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => max (f x) (g x)) l a :=
  show IsMaxFilter (fun x => Max.max (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => max_le_max hx hy) hg

/--
theorem `IsMinOn.max` / 定理 `IsMinOn.max`

English:
theorem IsMinOn.max
  given: (hf : IsMinOn f s a) (hg : IsMinOn g s a)
  proof: IsMinFilter.max hf hg

中文:
定理 IsMinOn.max
  条件: (hf : IsMinOn f s a) (hg : IsMinOn g s a)
  证明: IsMinFilter.max hf hg

Depends on / 依赖: IsMinFilter, IsMinFilter.max
-/
theorem IsMinOn.max (hf : IsMinOn f s a) (hg : IsMinOn g s a) :
    IsMinOn (fun x => max (f x) (g x)) s a :=
  IsMinFilter.max hf hg

/--
theorem `IsMaxOn.max` / 定理 `IsMaxOn.max`

English:
theorem IsMaxOn.max
  given: (hf : IsMaxOn f s a) (hg : IsMaxOn g s a)
  proof: IsMaxFilter.max hf hg

中文:
定理 IsMaxOn.max
  条件: (hf : IsMaxOn f s a) (hg : IsMaxOn g s a)
  证明: IsMaxFilter.max hf hg

Depends on / 依赖: IsMaxFilter, IsMaxFilter.max
-/
theorem IsMaxOn.max (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) :
    IsMaxOn (fun x => max (f x) (g x)) s a :=
  IsMaxFilter.max hf hg

/-! ### Extrema from monotonicity and antitonicity -/

variable {β : Type*} [LinearOrder α] [Preorder β] {a b c : α} {f : α -> β}

/--
lemma `isMaxOn_Ioo_of_mono_anti` / 引理 `isMaxOn_Ioo_of_mono_anti`

English:
lemma isMaxOn_Ioo_of_mono_anti
  given: (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Ico b c))
  proof: by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx.1)) g₀
  · refine h₁ (left_mem_Ico.2 (g₀.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

中文:
引理 isMaxOn_Ioo_of_mono_anti
  条件: (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Ico b c))
  证明: by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx.1)) g₀
  · refine h₁ (left_mem_Ico.2 (g₀.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

Depends on / 依赖: left_mem_Ico, right_mem_Ioc, trans_lt
-/
lemma isMaxOn_Ioo_of_mono_anti (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Ico b c)) :
    IsMaxOn f (Ioo a c) b := by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx.1)) g₀
  · refine h₁ (left_mem_Ico.2 (g₀.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

/--
lemma `isMinOn_Ioo_of_anti_mono` / 引理 `isMinOn_Ioo_of_anti_mono`

English:
lemma isMinOn_Ioo_of_anti_mono
  given: (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ico b c))
  proof: isMaxOn_Ioo_of_mono_anti (β := βᵒᵈ) h₀ h₁

中文:
引理 isMinOn_Ioo_of_anti_mono
  条件: (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ico b c))
  证明: isMaxOn_Ioo_of_mono_anti (β := βᵒᵈ) h₀ h₁

Depends on / 依赖: isMaxOn_Ioo_of_mono_anti
-/
lemma isMinOn_Ioo_of_anti_mono (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ico b c)) :
    IsMinOn f (Ioo a c) b :=
  isMaxOn_Ioo_of_mono_anti (β := βᵒᵈ) h₀ h₁

/--
lemma `isMaxOn_Ico_of_mono_anti` / 引理 `isMaxOn_Ico_of_mono_anti`

English:
lemma isMaxOn_Ico_of_mono_anti
  given: (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f (Ico b c))
  proof: by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Icc.2 (hx.1.trans g₀)) g₀
  · exact h₁ (left_mem_Ico.2 (g₀.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

中文:
引理 isMaxOn_Ico_of_mono_anti
  条件: (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f (Ico b c))
  证明: by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Icc.2 (hx.1.trans g₀)) g₀
  · exact h₁ (left_mem_Ico.2 (g₀.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

Depends on / 依赖: left_mem_Ico, right_mem_Icc
-/
lemma isMaxOn_Ico_of_mono_anti (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f (Ico b c)) :
    IsMaxOn f (Ico a c) b := by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Icc.2 (hx.1.trans g₀)) g₀
  · exact h₁ (left_mem_Ico.2 (g₀.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

/--
lemma `isMinOn_Ico_of_anti_mono` / 引理 `isMinOn_Ico_of_anti_mono`

English:
lemma isMinOn_Ico_of_anti_mono
  given: (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Ico b c))
  proof: isMaxOn_Ico_of_mono_anti (β := βᵒᵈ) h₀ h₁

中文:
引理 isMinOn_Ico_of_anti_mono
  条件: (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Ico b c))
  证明: isMaxOn_Ico_of_mono_anti (β := βᵒᵈ) h₀ h₁

Depends on / 依赖: isMaxOn_Ico_of_mono_anti
-/
lemma isMinOn_Ico_of_anti_mono (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Ico b c)) :
    IsMinOn f (Ico a c) b :=
  isMaxOn_Ico_of_mono_anti (β := βᵒᵈ) h₀ h₁

/--
lemma `isMaxOn_Ioc_of_mono_anti` / 引理 `isMaxOn_Ioc_of_mono_anti`

English:
lemma isMaxOn_Ioc_of_mono_anti
  given: (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Icc b c))
  proof: by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx.1)) g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

中文:
引理 isMaxOn_Ioc_of_mono_anti
  条件: (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Icc b c))
  证明: by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx.1)) g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

Depends on / 依赖: le.trans, left_mem_Icc, right_mem_Ioc, trans_lt
-/
lemma isMaxOn_Ioc_of_mono_anti (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Icc b c)) :
    IsMaxOn f (Ioc a c) b := by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx.1)) g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

/--
lemma `isMinOn_Ioc_of_anti_mono` / 引理 `isMinOn_Ioc_of_anti_mono`

English:
lemma isMinOn_Ioc_of_anti_mono
  given: (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Icc b c))
  proof: isMaxOn_Ioc_of_mono_anti (β := βᵒᵈ) h₀ h₁

中文:
引理 isMinOn_Ioc_of_anti_mono
  条件: (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Icc b c))
  证明: isMaxOn_Ioc_of_mono_anti (β := βᵒᵈ) h₀ h₁

Depends on / 依赖: isMaxOn_Ioc_of_mono_anti
-/
lemma isMinOn_Ioc_of_anti_mono (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Icc b c)) :
    IsMinOn f (Ioc a c) b :=
  isMaxOn_Ioc_of_mono_anti (β := βᵒᵈ) h₀ h₁

/--
lemma `isMaxOn_Icc_of_mono_anti` / 引理 `isMaxOn_Icc_of_mono_anti`

English:
lemma isMaxOn_Icc_of_mono_anti
  given: (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f (Icc b c))
  proof: by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Icc.2 (hx.1.trans g₀)) g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

中文:
引理 isMaxOn_Icc_of_mono_anti
  条件: (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f (Icc b c))
  证明: by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Icc.2 (hx.1.trans g₀)) g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

Depends on / 依赖: le.trans, left_mem_Icc, right_mem_Icc
-/
lemma isMaxOn_Icc_of_mono_anti (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f (Icc b c)) :
    IsMaxOn f (Icc a c) b := by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Icc.2 (hx.1.trans g₀)) g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

/--
lemma `isMinOn_Icc_of_anti_mono` / 引理 `isMinOn_Icc_of_anti_mono`

English:
lemma isMinOn_Icc_of_anti_mono
  given: (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Icc b c))
  proof: isMaxOn_Icc_of_mono_anti (β := βᵒᵈ) h₀ h₁

中文:
引理 isMinOn_Icc_of_anti_mono
  条件: (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Icc b c))
  证明: isMaxOn_Icc_of_mono_anti (β := βᵒᵈ) h₀ h₁

Depends on / 依赖: isMaxOn_Icc_of_mono_anti
-/
lemma isMinOn_Icc_of_anti_mono (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Icc b c)) :
    IsMinOn f (Icc a c) b :=
  isMaxOn_Icc_of_mono_anti (β := βᵒᵈ) h₀ h₁

/--
lemma `isMaxOn_Ioi_of_mono_anti` / 引理 `isMaxOn_Ioi_of_mono_anti`

English:
lemma isMaxOn_Ioi_of_mono_anti
  given: (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Ici b))
  proof: by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx)) g₀
  · exact h₁ self_mem_Ici g₀.le g₀.le

中文:
引理 isMaxOn_Ioi_of_mono_anti
  条件: (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Ici b))
  证明: by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx)) g₀
  · exact h₁ self_mem_Ici g₀.le g₀.le

Depends on / 依赖: right_mem_Ioc, self_mem_Ici, trans_lt
-/
lemma isMaxOn_Ioi_of_mono_anti (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Ici b)) :
    IsMaxOn f (Ioi a) b := by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx)) g₀
  · exact h₁ self_mem_Ici g₀.le g₀.le

/--
lemma `isMinOn_Ioi_of_anti_mono` / 引理 `isMinOn_Ioi_of_anti_mono`

English:
lemma isMinOn_Ioi_of_anti_mono
  given: (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ici b))
  proof: isMaxOn_Ioi_of_mono_anti (β := βᵒᵈ) h₀ h₁

中文:
引理 isMinOn_Ioi_of_anti_mono
  条件: (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ici b))
  证明: isMaxOn_Ioi_of_mono_anti (β := βᵒᵈ) h₀ h₁

Depends on / 依赖: isMaxOn_Ioi_of_mono_anti
-/
lemma isMinOn_Ioi_of_anti_mono (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ici b)) :
    IsMinOn f (Ioi a) b :=
  isMaxOn_Ioi_of_mono_anti (β := βᵒᵈ) h₀ h₁

/--
lemma `isMaxOn_Ici_of_mono_anti` / 引理 `isMaxOn_Ici_of_mono_anti`

English:
lemma isMaxOn_Ici_of_mono_anti
  given: (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f (Ici b))
  proof: by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx, g₀⟩ (right_mem_Icc.2 (hx.trans g₀)) g₀
  · exact h₁ self_mem_Ici g₀.le g₀.le

中文:
引理 isMaxOn_Ici_of_mono_anti
  条件: (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f (Ici b))
  证明: by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx, g₀⟩ (right_mem_Icc.2 (hx.trans g₀)) g₀
  · exact h₁ self_mem_Ici g₀.le g₀.le

Depends on / 依赖: hx.trans, right_mem_Icc, self_mem_Ici
-/
lemma isMaxOn_Ici_of_mono_anti (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f (Ici b)) :
    IsMaxOn f (Ici a) b := by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ ⟨hx, g₀⟩ (right_mem_Icc.2 (hx.trans g₀)) g₀
  · exact h₁ self_mem_Ici g₀.le g₀.le

/--
lemma `isMinOn_Ici_of_anti_mono` / 引理 `isMinOn_Ici_of_anti_mono`

English:
lemma isMinOn_Ici_of_anti_mono
  given: (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Ici b))
  proof: isMaxOn_Ici_of_mono_anti (β := βᵒᵈ) h₀ h₁

中文:
引理 isMinOn_Ici_of_anti_mono
  条件: (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Ici b))
  证明: isMaxOn_Ici_of_mono_anti (β := βᵒᵈ) h₀ h₁

Depends on / 依赖: isMaxOn_Ici_of_mono_anti
-/
lemma isMinOn_Ici_of_anti_mono (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Ici b)) :
    IsMinOn f (Ici a) b :=
  isMaxOn_Ici_of_mono_anti (β := βᵒᵈ) h₀ h₁

/--
lemma `isMaxOn_Iio_of_mono_anti` / 引理 `isMaxOn_Iio_of_mono_anti`

English:
lemma isMaxOn_Iio_of_mono_anti
  given: (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Ico b a))
  proof: by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ g₀ self_mem_Iic g₀
  · exact h₁ (left_mem_Ico.2 (g₀.trans hx)) ⟨g₀.le, hx⟩ g₀.le

中文:
引理 isMaxOn_Iio_of_mono_anti
  条件: (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Ico b a))
  证明: by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ g₀ self_mem_Iic g₀
  · exact h₁ (left_mem_Ico.2 (g₀.trans hx)) ⟨g₀.le, hx⟩ g₀.le

Depends on / 依赖: left_mem_Ico, self_mem_Iic
-/
lemma isMaxOn_Iio_of_mono_anti (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Ico b a)) :
    IsMaxOn f (Iio a) b := by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ g₀ self_mem_Iic g₀
  · exact h₁ (left_mem_Ico.2 (g₀.trans hx)) ⟨g₀.le, hx⟩ g₀.le

/--
lemma `isMinOn_Iio_of_anti_mono` / 引理 `isMinOn_Iio_of_anti_mono`

English:
lemma isMinOn_Iio_of_anti_mono
  given: (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Ico b a))
  proof: isMaxOn_Iio_of_mono_anti (β := βᵒᵈ) h₀ h₁

中文:
引理 isMinOn_Iio_of_anti_mono
  条件: (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Ico b a))
  证明: isMaxOn_Iio_of_mono_anti (β := βᵒᵈ) h₀ h₁

Depends on / 依赖: isMaxOn_Iio_of_mono_anti
-/
lemma isMinOn_Iio_of_anti_mono (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Ico b a)) :
    IsMinOn f (Iio a) b :=
  isMaxOn_Iio_of_mono_anti (β := βᵒᵈ) h₀ h₁

/--
lemma `isMaxOn_Iic_of_mono_anti` / 引理 `isMaxOn_Iic_of_mono_anti`

English:
lemma isMaxOn_Iic_of_mono_anti
  given: (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Icc b a))
  proof: by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ g₀ self_mem_Iic g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx)) ⟨g₀.le, hx⟩ g₀.le

中文:
引理 isMaxOn_Iic_of_mono_anti
  条件: (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Icc b a))
  证明: by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ g₀ self_mem_Iic g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx)) ⟨g₀.le, hx⟩ g₀.le

Depends on / 依赖: le.trans, left_mem_Icc, self_mem_Iic
-/
lemma isMaxOn_Iic_of_mono_anti (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Icc b a)) :
    IsMaxOn f (Iic a) b := by
  intro x hx
  by_cases! g₀ : x <= b
  · exact h₀ g₀ self_mem_Iic g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx)) ⟨g₀.le, hx⟩ g₀.le

/--
lemma `isMinOn_Iic_of_anti_mono` / 引理 `isMinOn_Iic_of_anti_mono`

English:
lemma isMinOn_Iic_of_anti_mono
  given: (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Icc b a))
  proof: isMaxOn_Iic_of_mono_anti (β := βᵒᵈ) h₀ h₁

中文:
引理 isMinOn_Iic_of_anti_mono
  条件: (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Icc b a))
  证明: isMaxOn_Iic_of_mono_anti (β := βᵒᵈ) h₀ h₁

Depends on / 依赖: isMaxOn_Iic_of_mono_anti
-/
lemma isMinOn_Iic_of_anti_mono (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Icc b a)) :
    IsMinOn f (Iic a) b :=
  isMaxOn_Iic_of_mono_anti (β := βᵒᵈ) h₀ h₁

/--
lemma `isMaxOn_univ_of_mono_anti` / 引理 `isMaxOn_univ_of_mono_anti`

English:
lemma isMaxOn_univ_of_mono_anti
  given: (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Ici b))
  proof: fun x _ => by rcases le_total x b <;> aesop

中文:
引理 isMaxOn_univ_of_mono_anti
  条件: (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Ici b))
  证明: fun x _ => by rcases le_total x b <;> aesop

Depends on / 依赖: le_total
-/
lemma isMaxOn_univ_of_mono_anti (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Ici b)) :
    IsMaxOn f univ b :=
  fun x _ => by rcases le_total x b <;> aesop

/--
lemma `isMinOn_univ_of_anti_mono` / 引理 `isMinOn_univ_of_anti_mono`

English:
lemma isMinOn_univ_of_anti_mono
  given: (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Ici b))
  proof: isMaxOn_univ_of_mono_anti (β := βᵒᵈ) h₀ h₁

中文:
引理 isMinOn_univ_of_anti_mono
  条件: (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Ici b))
  证明: isMaxOn_univ_of_mono_anti (β := βᵒᵈ) h₀ h₁

Depends on / 依赖: isMaxOn_univ_of_mono_anti
-/
lemma isMinOn_univ_of_anti_mono (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Ici b)) :
    IsMinOn f univ b :=
  isMaxOn_univ_of_mono_anti (β := βᵒᵈ) h₀ h₁

end LinearOrder

section Eventually



/--
theorem `Filter.EventuallyLE.isMaxFilter` / 定理 `Filter.EventuallyLE.isMaxFilter`

English:
theorem Filter.EventuallyLE.isMaxFilter
  statement: {α β : Type*} [Preorder β] {f g : α -> β} {a : α}
  proof: by
  refine hle.mp (h.mono fun x hf hgf => ?_)
  rw [← hfga]
  exact le_trans hgf hf

中文:
定理 Filter.EventuallyLE.isMaxFilter
  结论: {α β : 类型} [Preorder β] {f g : α -> β} {a : α}
  证明: by
  refine hle.mp (h.mono fun x hf hgf => ?_)
  rw [← hfga]
  exact le_trans hgf hf

Depends on / 依赖: h.mono, hle.mp, le_trans
-/
theorem Filter.EventuallyLE.isMaxFilter {α β : Type*} [Preorder β] {f g : α -> β} {a : α}
    {l : Filter α} (hle : g <=ᶠ[l] f) (hfga : f a = g a) (h : IsMaxFilter f l a) :
    IsMaxFilter g l a := by
  refine hle.mp (h.mono fun x hf hgf => ?_)
  rw [← hfga]
  exact le_trans hgf hf

/--
theorem `IsMaxFilter.congr` / 定理 `IsMaxFilter.congr`

English:
theorem IsMaxFilter.congr
  statement: {α β : Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α}
  proof: heq.symm.le.isMaxFilter hfga h

中文:
定理 IsMaxFilter.congr
  结论: {α β : 类型} [Preorder β] {f g : α -> β} {a : α} {l : Filter α}
  证明: heq.symm.le.isMaxFilter hfga h

Depends on / 依赖: heq.symm.le.isMaxFilter, isMaxFilter
-/
theorem IsMaxFilter.congr {α β : Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α}
    (h : IsMaxFilter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMaxFilter g l a :=
  heq.symm.le.isMaxFilter hfga h

/--
theorem `Filter.EventuallyEq.isMaxFilter_iff` / 定理 `Filter.EventuallyEq.isMaxFilter_iff`

English:
theorem Filter.EventuallyEq.isMaxFilter_iff
  statement: {α β : Type*} [Preorder β] {f g : α -> β} {a : α}
  proof: ⟨fun h => h.congr heq hfga, fun h => h.congr heq.symm hfga.symm⟩

中文:
定理 Filter.EventuallyEq.isMaxFilter_iff
  结论: {α β : 类型} [Preorder β] {f g : α -> β} {a : α}
  证明: ⟨fun h => h.congr heq hfga, fun h => h.congr heq.symm hfga.symm⟩

Depends on / 依赖: h.congr, heq.symm, hfga.symm
-/
theorem Filter.EventuallyEq.isMaxFilter_iff {α β : Type*} [Preorder β] {f g : α -> β} {a : α}
    {l : Filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMaxFilter f l a ↔ IsMaxFilter g l a :=
  ⟨fun h => h.congr heq hfga, fun h => h.congr heq.symm hfga.symm⟩

/--
theorem `Filter.EventuallyLE.isMinFilter` / 定理 `Filter.EventuallyLE.isMinFilter`

English:
theorem Filter.EventuallyLE.isMinFilter
  statement: {α β : Type*} [Preorder β] {f g : α -> β} {a : α}
  proof: @Filter.EventuallyLE.isMaxFilter _ βᵒᵈ _ _ _ _ _ hle hfga h

中文:
定理 Filter.EventuallyLE.isMinFilter
  结论: {α β : 类型} [Preorder β] {f g : α -> β} {a : α}
  证明: @Filter.EventuallyLE.isMaxFilter _ βᵒᵈ _ _ _ _ _ hle hfga h

Depends on / 依赖: EventuallyLE, Filter, Filter.EventuallyLE.isMaxFilter, isMaxFilter
-/
theorem Filter.EventuallyLE.isMinFilter {α β : Type*} [Preorder β] {f g : α -> β} {a : α}
    {l : Filter α} (hle : f <=ᶠ[l] g) (hfga : f a = g a) (h : IsMinFilter f l a) :
    IsMinFilter g l a :=
  @Filter.EventuallyLE.isMaxFilter _ βᵒᵈ _ _ _ _ _ hle hfga h

/--
theorem `IsMinFilter.congr` / 定理 `IsMinFilter.congr`

English:
theorem IsMinFilter.congr
  statement: {α β : Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α}
  proof: heq.le.isMinFilter hfga h

中文:
定理 IsMinFilter.congr
  结论: {α β : 类型} [Preorder β] {f g : α -> β} {a : α} {l : Filter α}
  证明: heq.le.isMinFilter hfga h

Depends on / 依赖: heq.le.isMinFilter, isMinFilter
-/
theorem IsMinFilter.congr {α β : Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α}
    (h : IsMinFilter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMinFilter g l a :=
  heq.le.isMinFilter hfga h

/--
theorem `Filter.EventuallyEq.isMinFilter_iff` / 定理 `Filter.EventuallyEq.isMinFilter_iff`

English:
theorem Filter.EventuallyEq.isMinFilter_iff
  statement: {α β : Type*} [Preorder β] {f g : α -> β} {a : α}
  proof: ⟨fun h => h.congr heq hfga, fun h => h.congr heq.symm hfga.symm⟩

中文:
定理 Filter.EventuallyEq.isMinFilter_iff
  结论: {α β : 类型} [Preorder β] {f g : α -> β} {a : α}
  证明: ⟨fun h => h.congr heq hfga, fun h => h.congr heq.symm hfga.symm⟩

Depends on / 依赖: h.congr, heq.symm, hfga.symm
-/
theorem Filter.EventuallyEq.isMinFilter_iff {α β : Type*} [Preorder β] {f g : α -> β} {a : α}
    {l : Filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMinFilter f l a ↔ IsMinFilter g l a :=
  ⟨fun h => h.congr heq hfga, fun h => h.congr heq.symm hfga.symm⟩

/--
theorem `IsExtrFilter.congr` / 定理 `IsExtrFilter.congr`

English:
theorem IsExtrFilter.congr
  statement: {α β : Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α}
  proof: by
  rw [IsExtrFilter] at *
  rwa [← heq.isMaxFilter_iff hfga, ← heq.isMinFilter_iff hfga]

中文:
定理 IsExtrFilter.congr
  结论: {α β : 类型} [Preorder β] {f g : α -> β} {a : α} {l : Filter α}
  证明: by
  rw [IsExtrFilter] at *
  rwa [← heq.isMaxFilter_iff hfga, ← heq.isMinFilter_iff hfga]

Depends on / 依赖: IsExtrFilter, heq.isMaxFilter_iff, heq.isMinFilter_iff, isMaxFilter_iff, isMinFilter_iff
-/
theorem IsExtrFilter.congr {α β : Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α}
    (h : IsExtrFilter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsExtrFilter g l a := by
  rw [IsExtrFilter] at *
  rwa [← heq.isMaxFilter_iff hfga, ← heq.isMinFilter_iff hfga]

/--
theorem `Filter.EventuallyEq.isExtrFilter_iff` / 定理 `Filter.EventuallyEq.isExtrFilter_iff`

English:
theorem Filter.EventuallyEq.isExtrFilter_iff
  statement: {α β : Type*} [Preorder β] {f g : α -> β} {a : α}
  proof: ⟨fun h => h.congr heq hfga, fun h => h.congr heq.symm hfga.symm⟩

中文:
定理 Filter.EventuallyEq.isExtrFilter_iff
  结论: {α β : 类型} [Preorder β] {f g : α -> β} {a : α}
  证明: ⟨fun h => h.congr heq hfga, fun h => h.congr heq.symm hfga.symm⟩

Depends on / 依赖: h.congr, heq.symm, hfga.symm
-/
theorem Filter.EventuallyEq.isExtrFilter_iff {α β : Type*} [Preorder β] {f g : α -> β} {a : α}
    {l : Filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsExtrFilter f l a ↔ IsExtrFilter g l a :=
  ⟨fun h => h.congr heq hfga, fun h => h.congr heq.symm hfga.symm⟩

end Eventually

/-! ### `isMaxOn`/`isMinOn` imply `ciSup`/`ciInf` -/


section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {f : β -> α} {s : Set β} {x₀ : β}

/--
theorem `IsMaxOn.iSup_eq` / 定理 `IsMaxOn.iSup_eq`

English:
theorem IsMaxOn.iSup_eq
  given: (hx₀ : x₀ in s) (h : IsMaxOn f s x₀)
  statement: ⨆ x : s, f x = f x₀
  proof: haveI : Nonempty s := ⟨⟨x₀, hx₀⟩⟩
  ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun x => h x.2) fun _w hw => ⟨⟨x₀, hx₀⟩, hw⟩

中文:
定理 IsMaxOn.iSup_eq
  条件: (hx₀ : x₀ in s) (h : IsMaxOn f s x₀)
  结论: ⨆ x : s, f x = f x₀
  证明: haveI : Nonempty s := ⟨⟨x₀, hx₀⟩⟩
  ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun x => h x.2) fun _w hw => ⟨⟨x₀, hx₀⟩, hw⟩

Depends on / 依赖: Nonempty, ciSup_eq_of_forall_le_of_forall_lt_exists_gt
-/
theorem IsMaxOn.iSup_eq (hx₀ : x₀ in s) (h : IsMaxOn f s x₀) : ⨆ x : s, f x = f x₀ :=
  haveI : Nonempty s := ⟨⟨x₀, hx₀⟩⟩
  ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun x => h x.2) fun _w hw => ⟨⟨x₀, hx₀⟩, hw⟩

/--
theorem `IsMinOn.iInf_eq` / 定理 `IsMinOn.iInf_eq`

English:
theorem IsMinOn.iInf_eq
  given: (hx₀ : x₀ in s) (h : IsMinOn f s x₀)
  statement: ⨅ x : s, f x = f x₀
  proof: @IsMaxOn.iSup_eq αᵒᵈ β _ _ _ _ hx₀ h

中文:
定理 IsMinOn.iInf_eq
  条件: (hx₀ : x₀ in s) (h : IsMinOn f s x₀)
  结论: ⨅ x : s, f x = f x₀
  证明: @IsMaxOn.iSup_eq αᵒᵈ β _ _ _ _ hx₀ h

Depends on / 依赖: IsMaxOn, IsMaxOn.iSup_eq, iSup_eq
-/
theorem IsMinOn.iInf_eq (hx₀ : x₀ in s) (h : IsMinOn f s x₀) : ⨅ x : s, f x = f x₀ :=
  @IsMaxOn.iSup_eq αᵒᵈ β _ _ _ _ hx₀ h

end ConditionallyCompleteLinearOrder

/-! ### Value of `Finset.sup` / `Finset.inf` -/

section SemilatticeSup

variable [SemilatticeSup β] [OrderBot β] {D : α -> β} {s : Finset α}

/--
theorem `sup_eq_of_isMaxOn` / 定理 `sup_eq_of_isMaxOn`

English:
theorem sup_eq_of_isMaxOn
  given: {a : α} (hmem : a in s) (hmax : IsMaxOn D s a)
  statement: s.sup D = D a
  proof: (Finset.sup_le hmax).antisymm (Finset.le_sup hmem)

中文:
定理 sup_eq_of_isMaxOn
  条件: {a : α} (hmem : a in s) (hmax : IsMaxOn D s a)
  结论: s.sup D = D a
  证明: (Finset.sup_le hmax).antisymm (Finset.le_sup hmem)

Depends on / 依赖: Finset, Finset.le_sup, Finset.sup_le, antisymm, le_sup, sup_le
-/
theorem sup_eq_of_isMaxOn {a : α} (hmem : a in s) (hmax : IsMaxOn D s a) : s.sup D = D a :=
  (Finset.sup_le hmax).antisymm (Finset.le_sup hmem)

/--
theorem `sup_eq_of_max` / 定理 `sup_eq_of_max`

English:
theorem sup_eq_of_max
  statement: [Nonempty α] {b : β} (hb : b in Set.range D) (hmem : D.invFun b in s)
  proof: by
  obtain ⟨a, rfl⟩ := hb
  rw [← Function.apply_invFun_apply (f := D)]
  apply sup_eq_of_isMaxOn hmem; intro
  rw [Function.apply_invFun_apply (f := D)]; apply hmax

中文:
定理 sup_eq_of_max
  结论: [Nonempty α] {b : β} (hb : b in Set.range D) (hmem : D.invFun b in s)
  证明: by
  obtain ⟨a, rfl⟩ := hb
  rw [← Function.apply_invFun_apply (f := D)]
  apply sup_eq_of_isMaxOn hmem; intro
  rw [Function.apply_invFun_apply (f := D)]; apply hmax

Depends on / 依赖: Function, Function.apply_invFun_apply, apply_invFun_apply, sup_eq_of_isMaxOn
-/
theorem sup_eq_of_max [Nonempty α] {b : β} (hb : b in Set.range D) (hmem : D.invFun b in s)
    (hmax : forall a in s, D a <= b) : s.sup D = b := by
  obtain ⟨a, rfl⟩ := hb
  rw [← Function.apply_invFun_apply (f := D)]
  apply sup_eq_of_isMaxOn hmem; intro
  rw [Function.apply_invFun_apply (f := D)]; apply hmax

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf β] [OrderTop β] {D : α -> β} {s : Finset α}

/--
theorem `inf_eq_of_isMinOn` / 定理 `inf_eq_of_isMinOn`

English:
theorem inf_eq_of_isMinOn
  given: {a : α} (hmem : a in s) (hmax : IsMinOn D s a)
  statement: s.inf D = D a
  proof: sup_eq_of_isMaxOn (α := αᵒᵈ) (β := βᵒᵈ) hmem hmax.dual

中文:
定理 inf_eq_of_isMinOn
  条件: {a : α} (hmem : a in s) (hmax : IsMinOn D s a)
  结论: s.inf D = D a
  证明: sup_eq_of_isMaxOn (α := αᵒᵈ) (β := βᵒᵈ) hmem hmax.dual

Depends on / 依赖: hmax.dual, sup_eq_of_isMaxOn
-/
theorem inf_eq_of_isMinOn {a : α} (hmem : a in s) (hmax : IsMinOn D s a) : s.inf D = D a :=
  sup_eq_of_isMaxOn (α := αᵒᵈ) (β := βᵒᵈ) hmem hmax.dual

/--
theorem `inf_eq_of_min` / 定理 `inf_eq_of_min`

English:
theorem inf_eq_of_min
  statement: [Nonempty α] {b : β} (hb : b in Set.range D) (hmem : D.invFun b in s)
  proof: sup_eq_of_max (α := αᵒᵈ) (β := βᵒᵈ) hb hmem hmin

中文:
定理 inf_eq_of_min
  结论: [Nonempty α] {b : β} (hb : b in Set.range D) (hmem : D.invFun b in s)
  证明: sup_eq_of_max (α := αᵒᵈ) (β := βᵒᵈ) hb hmem hmin

Depends on / 依赖: sup_eq_of_max
-/
theorem inf_eq_of_min [Nonempty α] {b : β} (hb : b in Set.range D) (hmem : D.invFun b in s)
    (hmin : forall a in s, b <= D a) : s.inf D = b :=
  sup_eq_of_max (α := αᵒᵈ) (β := βᵒᵈ) hb hmem hmin

end SemilatticeInf
