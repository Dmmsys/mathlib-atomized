/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Lattice

/-!
# Monovariance of functions

Two functions *vary together* if a strict change in the first implies a change in the second.

This is in some sense a way to say that two functions `f : ι → α`, `g : ι → β` are "monotone
together", without actually having an order on `ι`.

This condition comes up in the rearrangement inequality. See `Algebra.Order.Rearrangement`.

## Main declarations

* `Monovary f g`: `f` monovaries with `g`. If `g i < g j`, then `f i ≤ f j`.
* `Antivary f g`: `f` antivaries with `g`. If `g i < g j`, then `f j ≤ f i`.
* `MonovaryOn f g s`: `f` monovaries with `g` on `s`.
* `AntivaryOn f g s`: `f` antivaries with `g` on `s`.
-/

@[expose] public section


open Function Set

variable {ι ι' α β γ : Type*}

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] {f : ι -> α} {f' : α -> γ} {g : ι -> β}
  {s t : Set ι}

/--
Definition of `Monovary` / `Monovary` 的定义

English:
definition Monovary
  signature: (f : ι -> α) (g : ι -> β)
  body: forall ⦃i j⦄, g i < g j -> f i <= f j

中文:
定义 Monovary
  签名: (f : ι -> α) (g : ι -> β)
  定义体: forall ⦃i j⦄, g i < g j -> f i <= f j
-/
def Monovary (f : ι -> α) (g : ι -> β) : Prop :=
  forall ⦃i j⦄, g i < g j -> f i <= f j

/--
Definition of `Antivary` / `Antivary` 的定义

English:
definition Antivary
  signature: (f : ι -> α) (g : ι -> β)
  body: forall ⦃i j⦄, g i < g j -> f j <= f i

中文:
定义 Antivary
  签名: (f : ι -> α) (g : ι -> β)
  定义体: forall ⦃i j⦄, g i < g j -> f j <= f i
-/
def Antivary (f : ι -> α) (g : ι -> β) : Prop :=
  forall ⦃i j⦄, g i < g j -> f j <= f i

/--
Definition of `MonovaryOn` / `MonovaryOn` 的定义

English:
definition MonovaryOn
  signature: (f : ι -> α) (g : ι -> β) (s : Set ι)
  body: forall ⦃i⦄ (_ : i in s) ⦃j⦄ (_ : j in s), g i < g j -> f i <= f j

中文:
定义 MonovaryOn
  签名: (f : ι -> α) (g : ι -> β) (s : Set ι)
  定义体: forall ⦃i⦄ (_ : i in s) ⦃j⦄ (_ : j in s), g i < g j -> f i <= f j
-/
def MonovaryOn (f : ι -> α) (g : ι -> β) (s : Set ι) : Prop :=
  forall ⦃i⦄ (_ : i in s) ⦃j⦄ (_ : j in s), g i < g j -> f i <= f j

/--
Definition of `AntivaryOn` / `AntivaryOn` 的定义

English:
definition AntivaryOn
  signature: (f : ι -> α) (g : ι -> β) (s : Set ι)
  body: forall ⦃i⦄ (_ : i in s) ⦃j⦄ (_ : j in s), g i < g j -> f j <= f i

中文:
定义 AntivaryOn
  签名: (f : ι -> α) (g : ι -> β) (s : Set ι)
  定义体: forall ⦃i⦄ (_ : i in s) ⦃j⦄ (_ : j in s), g i < g j -> f j <= f i
-/
def AntivaryOn (f : ι -> α) (g : ι -> β) (s : Set ι) : Prop :=
  forall ⦃i⦄ (_ : i in s) ⦃j⦄ (_ : j in s), g i < g j -> f j <= f i

/--
theorem `Monovary.monovaryOn` / 定理 `Monovary.monovaryOn`

English:
theorem Monovary.monovaryOn
  given: (h : Monovary f g) (s : Set ι)
  statement: MonovaryOn f g s
  proof: fun _ _ _ _ hij => h hij

中文:
定理 Monovary.monovaryOn
  条件: (h : Monovary f g) (s : Set ι)
  结论: MonovaryOn f g s
  证明: fun _ _ _ _ hij => h hij
-/
protected theorem Monovary.monovaryOn (h : Monovary f g) (s : Set ι) : MonovaryOn f g s :=
  fun _ _ _ _ hij => h hij

/--
theorem `Antivary.antivaryOn` / 定理 `Antivary.antivaryOn`

English:
theorem Antivary.antivaryOn
  given: (h : Antivary f g) (s : Set ι)
  statement: AntivaryOn f g s
  proof: fun _ _ _ _ hij => h hij

@[simp]

中文:
定理 Antivary.antivaryOn
  条件: (h : Antivary f g) (s : Set ι)
  结论: AntivaryOn f g s
  证明: fun _ _ _ _ hij => h hij

@[simp]
-/
protected theorem Antivary.antivaryOn (h : Antivary f g) (s : Set ι) : AntivaryOn f g s :=
  fun _ _ _ _ hij => h hij

@[simp]
/--
theorem `MonovaryOn.empty` / 定理 `MonovaryOn.empty`

English:
theorem MonovaryOn.empty
  statement: MonovaryOn f g ∅
  proof: fun _ => False.elim

@[simp]

中文:
定理 MonovaryOn.empty
  结论: MonovaryOn f g ∅
  证明: fun _ => False.elim

@[simp]

Depends on / 依赖: False.elim
-/
theorem MonovaryOn.empty : MonovaryOn f g ∅ := fun _ => False.elim

@[simp]
/--
theorem `AntivaryOn.empty` / 定理 `AntivaryOn.empty`

English:
theorem AntivaryOn.empty
  statement: AntivaryOn f g ∅
  proof: fun _ => False.elim

@[simp]

中文:
定理 AntivaryOn.empty
  结论: AntivaryOn f g ∅
  证明: fun _ => False.elim

@[simp]

Depends on / 依赖: False.elim
-/
theorem AntivaryOn.empty : AntivaryOn f g ∅ := fun _ => False.elim

@[simp]
/--
theorem `monovaryOn_univ` / 定理 `monovaryOn_univ`

English:
theorem monovaryOn_univ
  statement: MonovaryOn f g univ ↔ Monovary f g
  proof: ⟨fun h _ _ => h trivial trivial, fun h _ _ _ _ hij => h hij⟩

@[simp]

中文:
定理 monovaryOn_univ
  结论: MonovaryOn f g univ ↔ Monovary f g
  证明: ⟨fun h _ _ => h trivial trivial, fun h _ _ _ _ hij => h hij⟩

@[simp]
-/
theorem monovaryOn_univ : MonovaryOn f g univ ↔ Monovary f g :=
  ⟨fun h _ _ => h trivial trivial, fun h _ _ _ _ hij => h hij⟩

@[simp]
/--
theorem `antivaryOn_univ` / 定理 `antivaryOn_univ`

English:
theorem antivaryOn_univ
  statement: AntivaryOn f g univ ↔ Antivary f g
  proof: ⟨fun h _ _ => h trivial trivial, fun h _ _ _ _ hij => h hij⟩

中文:
定理 antivaryOn_univ
  结论: AntivaryOn f g univ ↔ Antivary f g
  证明: ⟨fun h _ _ => h trivial trivial, fun h _ _ _ _ hij => h hij⟩
-/
theorem antivaryOn_univ : AntivaryOn f g univ ↔ Antivary f g :=
  ⟨fun h _ _ => h trivial trivial, fun h _ _ _ _ hij => h hij⟩

/--
lemma `monovaryOn_iff_monovary` / 引理 `monovaryOn_iff_monovary`

English:
lemma monovaryOn_iff_monovary
  statement: MonovaryOn f g s ↔ Monovary (fun i : s => f i) fun i => g i
  proof: by
  simp [Monovary, MonovaryOn]

中文:
引理 monovaryOn_iff_monovary
  结论: MonovaryOn f g s ↔ Monovary (fun i : s => f i) fun i => g i
  证明: by
  simp [Monovary, MonovaryOn]

Depends on / 依赖: Monovary, MonovaryOn
-/
lemma monovaryOn_iff_monovary : MonovaryOn f g s ↔ Monovary (fun i : s => f i) fun i => g i := by
  simp [Monovary, MonovaryOn]

/--
lemma `antivaryOn_iff_antivary` / 引理 `antivaryOn_iff_antivary`

English:
lemma antivaryOn_iff_antivary
  statement: AntivaryOn f g s ↔ Antivary (fun i : s => f i) fun i => g i
  proof: by
  simp [Antivary, AntivaryOn]

中文:
引理 antivaryOn_iff_antivary
  结论: AntivaryOn f g s ↔ Antivary (fun i : s => f i) fun i => g i
  证明: by
  simp [Antivary, AntivaryOn]

Depends on / 依赖: Antivary, AntivaryOn
-/
lemma antivaryOn_iff_antivary : AntivaryOn f g s ↔ Antivary (fun i : s => f i) fun i => g i := by
  simp [Antivary, AntivaryOn]

/--
theorem `MonovaryOn.subset` / 定理 `MonovaryOn.subset`

English:
theorem MonovaryOn.subset
  given: (hst : s subseteq t) (h : MonovaryOn f g t)
  statement: MonovaryOn f g s
  proof: fun _ hi _ hj => h (hst hi) (hst hj)

中文:
定理 MonovaryOn.subset
  条件: (hst : s subseteq t) (h : MonovaryOn f g t)
  结论: MonovaryOn f g s
  证明: fun _ hi _ hj => h (hst hi) (hst hj)
-/
protected theorem MonovaryOn.subset (hst : s subseteq t) (h : MonovaryOn f g t) : MonovaryOn f g s :=
  fun _ hi _ hj => h (hst hi) (hst hj)

/--
theorem `AntivaryOn.subset` / 定理 `AntivaryOn.subset`

English:
theorem AntivaryOn.subset
  given: (hst : s subseteq t) (h : AntivaryOn f g t)
  statement: AntivaryOn f g s
  proof: fun _ hi _ hj => h (hst hi) (hst hj)

中文:
定理 AntivaryOn.subset
  条件: (hst : s subseteq t) (h : AntivaryOn f g t)
  结论: AntivaryOn f g s
  证明: fun _ hi _ hj => h (hst hi) (hst hj)
-/
protected theorem AntivaryOn.subset (hst : s subseteq t) (h : AntivaryOn f g t) : AntivaryOn f g s :=
  fun _ hi _ hj => h (hst hi) (hst hj)

/--
theorem `monovary_const_left` / 定理 `monovary_const_left`

English:
theorem monovary_const_left
  given: (g : ι -> β) (a : α)
  statement: Monovary (const ι a) g
  proof: fun _ _ _ => le_rfl

中文:
定理 monovary_const_left
  条件: (g : ι -> β) (a : α)
  结论: Monovary (const ι a) g
  证明: fun _ _ _ => le_rfl

Depends on / 依赖: le_rfl
-/
theorem monovary_const_left (g : ι -> β) (a : α) : Monovary (const ι a) g := fun _ _ _ => le_rfl

/--
theorem `antivary_const_left` / 定理 `antivary_const_left`

English:
theorem antivary_const_left
  given: (g : ι -> β) (a : α)
  statement: Antivary (const ι a) g
  proof: fun _ _ _ => le_rfl

中文:
定理 antivary_const_left
  条件: (g : ι -> β) (a : α)
  结论: Antivary (const ι a) g
  证明: fun _ _ _ => le_rfl

Depends on / 依赖: le_rfl
-/
theorem antivary_const_left (g : ι -> β) (a : α) : Antivary (const ι a) g := fun _ _ _ => le_rfl

/--
theorem `monovary_const_right` / 定理 `monovary_const_right`

English:
theorem monovary_const_right
  given: (f : ι -> α) (b : β)
  statement: Monovary f (const ι b)
  proof: fun _ _ h =>
  (h.ne rfl).elim

中文:
定理 monovary_const_right
  条件: (f : ι -> α) (b : β)
  结论: Monovary f (const ι b)
  证明: fun _ _ h =>
  (h.ne rfl).elim
-/
theorem monovary_const_right (f : ι -> α) (b : β) : Monovary f (const ι b) := fun _ _ h =>
  (h.ne rfl).elim

/--
theorem `antivary_const_right` / 定理 `antivary_const_right`

English:
theorem antivary_const_right
  given: (f : ι -> α) (b : β)
  statement: Antivary f (const ι b)
  proof: fun _ _ h =>
  (h.ne rfl).elim

中文:
定理 antivary_const_right
  条件: (f : ι -> α) (b : β)
  结论: Antivary f (const ι b)
  证明: fun _ _ h =>
  (h.ne rfl).elim
-/
theorem antivary_const_right (f : ι -> α) (b : β) : Antivary f (const ι b) := fun _ _ h =>
  (h.ne rfl).elim

/--
theorem `monovary_self` / 定理 `monovary_self`

English:
theorem monovary_self
  given: (f : ι -> α)
  statement: Monovary f f
  proof: fun _ _ => le_of_lt

中文:
定理 monovary_self
  条件: (f : ι -> α)
  结论: Monovary f f
  证明: fun _ _ => le_of_lt

Depends on / 依赖: le_of_lt
-/
theorem monovary_self (f : ι -> α) : Monovary f f := fun _ _ => le_of_lt

/--
theorem `monovaryOn_self` / 定理 `monovaryOn_self`

English:
theorem monovaryOn_self
  given: (f : ι -> α) (s : Set ι)
  statement: MonovaryOn f f s
  proof: fun _ _ _ _ => le_of_lt

中文:
定理 monovaryOn_self
  条件: (f : ι -> α) (s : Set ι)
  结论: MonovaryOn f f s
  证明: fun _ _ _ _ => le_of_lt

Depends on / 依赖: le_of_lt
-/
theorem monovaryOn_self (f : ι -> α) (s : Set ι) : MonovaryOn f f s := fun _ _ _ _ => le_of_lt

/--
theorem `Subsingleton.monovary` / 定理 `Subsingleton.monovary`

English:
theorem Subsingleton.monovary
  given: [Subsingleton ι] (f : ι -> α) (g : ι -> β)
  statement: Monovary f g
  proof: fun _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim

中文:
定理 Subsingleton.monovary
  条件: [Subsingleton ι] (f : ι -> α) (g : ι -> β)
  结论: Monovary f g
  证明: fun _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim
-/
protected theorem Subsingleton.monovary [Subsingleton ι] (f : ι -> α) (g : ι -> β) : Monovary f g :=
  fun _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim

/--
theorem `Subsingleton.antivary` / 定理 `Subsingleton.antivary`

English:
theorem Subsingleton.antivary
  given: [Subsingleton ι] (f : ι -> α) (g : ι -> β)
  statement: Antivary f g
  proof: fun _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim

中文:
定理 Subsingleton.antivary
  条件: [Subsingleton ι] (f : ι -> α) (g : ι -> β)
  结论: Antivary f g
  证明: fun _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim
-/
protected theorem Subsingleton.antivary [Subsingleton ι] (f : ι -> α) (g : ι -> β) : Antivary f g :=
  fun _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim

/--
theorem `Subsingleton.monovaryOn` / 定理 `Subsingleton.monovaryOn`

English:
theorem Subsingleton.monovaryOn
  given: [Subsingleton ι] (f : ι -> α) (g : ι -> β) (s : Set ι)
  proof: fun _ _ _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim

中文:
定理 Subsingleton.monovaryOn
  条件: [Subsingleton ι] (f : ι -> α) (g : ι -> β) (s : Set ι)
  证明: fun _ _ _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim
-/
protected theorem Subsingleton.monovaryOn [Subsingleton ι] (f : ι -> α) (g : ι -> β) (s : Set ι) :
    MonovaryOn f g s := fun _ _ _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim

/--
theorem `Subsingleton.antivaryOn` / 定理 `Subsingleton.antivaryOn`

English:
theorem Subsingleton.antivaryOn
  given: [Subsingleton ι] (f : ι -> α) (g : ι -> β) (s : Set ι)
  proof: fun _ _ _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim

中文:
定理 Subsingleton.antivaryOn
  条件: [Subsingleton ι] (f : ι -> α) (g : ι -> β) (s : Set ι)
  证明: fun _ _ _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim
-/
protected theorem Subsingleton.antivaryOn [Subsingleton ι] (f : ι -> α) (g : ι -> β) (s : Set ι) :
    AntivaryOn f g s := fun _ _ _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim

/--
theorem `monovaryOn_const_left` / 定理 `monovaryOn_const_left`

English:
theorem monovaryOn_const_left
  given: (g : ι -> β) (a : α) (s : Set ι)
  statement: MonovaryOn (const ι a) g s
  proof: fun _ _ _ _ _ => le_rfl

中文:
定理 monovaryOn_const_left
  条件: (g : ι -> β) (a : α) (s : Set ι)
  结论: MonovaryOn (const ι a) g s
  证明: fun _ _ _ _ _ => le_rfl

Depends on / 依赖: le_rfl
-/
theorem monovaryOn_const_left (g : ι -> β) (a : α) (s : Set ι) : MonovaryOn (const ι a) g s :=
  fun _ _ _ _ _ => le_rfl

/--
theorem `antivaryOn_const_left` / 定理 `antivaryOn_const_left`

English:
theorem antivaryOn_const_left
  given: (g : ι -> β) (a : α) (s : Set ι)
  statement: AntivaryOn (const ι a) g s
  proof: fun _ _ _ _ _ => le_rfl

中文:
定理 antivaryOn_const_left
  条件: (g : ι -> β) (a : α) (s : Set ι)
  结论: AntivaryOn (const ι a) g s
  证明: fun _ _ _ _ _ => le_rfl

Depends on / 依赖: le_rfl
-/
theorem antivaryOn_const_left (g : ι -> β) (a : α) (s : Set ι) : AntivaryOn (const ι a) g s :=
  fun _ _ _ _ _ => le_rfl

/--
theorem `monovaryOn_const_right` / 定理 `monovaryOn_const_right`

English:
theorem monovaryOn_const_right
  given: (f : ι -> α) (b : β) (s : Set ι)
  statement: MonovaryOn f (const ι b) s
  proof: fun _ _ _ _ h => (h.ne rfl).elim

中文:
定理 monovaryOn_const_right
  条件: (f : ι -> α) (b : β) (s : Set ι)
  结论: MonovaryOn f (const ι b) s
  证明: fun _ _ _ _ h => (h.ne rfl).elim

Depends on / 依赖: h.ne
-/
theorem monovaryOn_const_right (f : ι -> α) (b : β) (s : Set ι) : MonovaryOn f (const ι b) s :=
  fun _ _ _ _ h => (h.ne rfl).elim

/--
theorem `antivaryOn_const_right` / 定理 `antivaryOn_const_right`

English:
theorem antivaryOn_const_right
  given: (f : ι -> α) (b : β) (s : Set ι)
  statement: AntivaryOn f (const ι b) s
  proof: fun _ _ _ _ h => (h.ne rfl).elim

中文:
定理 antivaryOn_const_right
  条件: (f : ι -> α) (b : β) (s : Set ι)
  结论: AntivaryOn f (const ι b) s
  证明: fun _ _ _ _ h => (h.ne rfl).elim

Depends on / 依赖: h.ne
-/
theorem antivaryOn_const_right (f : ι -> α) (b : β) (s : Set ι) : AntivaryOn f (const ι b) s :=
  fun _ _ _ _ h => (h.ne rfl).elim

/--
theorem `Monovary.comp_right` / 定理 `Monovary.comp_right`

English:
theorem Monovary.comp_right
  given: (h : Monovary f g) (k : ι' -> ι)
  statement: Monovary (f ∘ k) (g ∘ k)
  proof: fun _ _ hij => h hij

中文:
定理 Monovary.comp_right
  条件: (h : Monovary f g) (k : ι' -> ι)
  结论: Monovary (f ∘ k) (g ∘ k)
  证明: fun _ _ hij => h hij
-/
theorem Monovary.comp_right (h : Monovary f g) (k : ι' -> ι) : Monovary (f ∘ k) (g ∘ k) :=
  fun _ _ hij => h hij

/--
theorem `Antivary.comp_right` / 定理 `Antivary.comp_right`

English:
theorem Antivary.comp_right
  given: (h : Antivary f g) (k : ι' -> ι)
  statement: Antivary (f ∘ k) (g ∘ k)
  proof: fun _ _ hij => h hij

中文:
定理 Antivary.comp_right
  条件: (h : Antivary f g) (k : ι' -> ι)
  结论: Antivary (f ∘ k) (g ∘ k)
  证明: fun _ _ hij => h hij
-/
theorem Antivary.comp_right (h : Antivary f g) (k : ι' -> ι) : Antivary (f ∘ k) (g ∘ k) :=
  fun _ _ hij => h hij

/--
theorem `MonovaryOn.comp_right` / 定理 `MonovaryOn.comp_right`

English:
theorem MonovaryOn.comp_right
  given: (h : MonovaryOn f g s) (k : ι' -> ι)
  proof: fun _ hi _ hj => h hi hj

中文:
定理 MonovaryOn.comp_right
  条件: (h : MonovaryOn f g s) (k : ι' -> ι)
  证明: fun _ hi _ hj => h hi hj
-/
theorem MonovaryOn.comp_right (h : MonovaryOn f g s) (k : ι' -> ι) :
    MonovaryOn (f ∘ k) (g ∘ k) (k ⁻¹' s) := fun _ hi _ hj => h hi hj

/--
theorem `AntivaryOn.comp_right` / 定理 `AntivaryOn.comp_right`

English:
theorem AntivaryOn.comp_right
  given: (h : AntivaryOn f g s) (k : ι' -> ι)
  proof: fun _ hi _ hj => h hi hj

中文:
定理 AntivaryOn.comp_right
  条件: (h : AntivaryOn f g s) (k : ι' -> ι)
  证明: fun _ hi _ hj => h hi hj
-/
theorem AntivaryOn.comp_right (h : AntivaryOn f g s) (k : ι' -> ι) :
    AntivaryOn (f ∘ k) (g ∘ k) (k ⁻¹' s) := fun _ hi _ hj => h hi hj

/--
theorem `Monovary.comp_monotone_left` / 定理 `Monovary.comp_monotone_left`

English:
theorem Monovary.comp_monotone_left
  given: (h : Monovary f g) (hf : Monotone f')
  statement: Monovary (f' ∘ f) g
  proof: fun _ _ hij => hf h hij

中文:
定理 Monovary.comp_monotone_left
  条件: (h : Monovary f g) (hf : Monotone f')
  结论: Monovary (f' ∘ f) g
  证明: fun _ _ hij => hf h hij
-/
theorem Monovary.comp_monotone_left (h : Monovary f g) (hf : Monotone f') : Monovary (f' ∘ f) g :=
fun _ _ hij => hf h hij

/--
theorem `Monovary.comp_antitone_left` / 定理 `Monovary.comp_antitone_left`

English:
theorem Monovary.comp_antitone_left
  given: (h : Monovary f g) (hf : Antitone f')
  statement: Antivary (f' ∘ f) g
  proof: fun _ _ hij => hf h hij

中文:
定理 Monovary.comp_antitone_left
  条件: (h : Monovary f g) (hf : Antitone f')
  结论: Antivary (f' ∘ f) g
  证明: fun _ _ hij => hf h hij
-/
theorem Monovary.comp_antitone_left (h : Monovary f g) (hf : Antitone f') : Antivary (f' ∘ f) g :=
fun _ _ hij => hf h hij

/--
theorem `Antivary.comp_monotone_left` / 定理 `Antivary.comp_monotone_left`

English:
theorem Antivary.comp_monotone_left
  given: (h : Antivary f g) (hf : Monotone f')
  statement: Antivary (f' ∘ f) g
  proof: fun _ _ hij => hf h hij

中文:
定理 Antivary.comp_monotone_left
  条件: (h : Antivary f g) (hf : Monotone f')
  结论: Antivary (f' ∘ f) g
  证明: fun _ _ hij => hf h hij
-/
theorem Antivary.comp_monotone_left (h : Antivary f g) (hf : Monotone f') : Antivary (f' ∘ f) g :=
fun _ _ hij => hf h hij

/--
theorem `Antivary.comp_antitone_left` / 定理 `Antivary.comp_antitone_left`

English:
theorem Antivary.comp_antitone_left
  given: (h : Antivary f g) (hf : Antitone f')
  statement: Monovary (f' ∘ f) g
  proof: fun _ _ hij => hf h hij

中文:
定理 Antivary.comp_antitone_left
  条件: (h : Antivary f g) (hf : Antitone f')
  结论: Monovary (f' ∘ f) g
  证明: fun _ _ hij => hf h hij
-/
theorem Antivary.comp_antitone_left (h : Antivary f g) (hf : Antitone f') : Monovary (f' ∘ f) g :=
fun _ _ hij => hf h hij

/--
theorem `MonovaryOn.comp_monotone_on_left` / 定理 `MonovaryOn.comp_monotone_on_left`

English:
theorem MonovaryOn.comp_monotone_on_left
  given: (h : MonovaryOn f g s) (hf : Monotone f')
  proof: fun _ hi _ hj hij => hf h hi hj hij

中文:
定理 MonovaryOn.comp_monotone_on_left
  条件: (h : MonovaryOn f g s) (hf : Monotone f')
  证明: fun _ hi _ hj hij => hf h hi hj hij
-/
theorem MonovaryOn.comp_monotone_on_left (h : MonovaryOn f g s) (hf : Monotone f') :
MonovaryOn (f' ∘ f) g s := fun _ hi _ hj hij => hf h hi hj hij

/--
theorem `MonovaryOn.comp_antitone_on_left` / 定理 `MonovaryOn.comp_antitone_on_left`

English:
theorem MonovaryOn.comp_antitone_on_left
  given: (h : MonovaryOn f g s) (hf : Antitone f')
  proof: fun _ hi _ hj hij => hf h hi hj hij

中文:
定理 MonovaryOn.comp_antitone_on_left
  条件: (h : MonovaryOn f g s) (hf : Antitone f')
  证明: fun _ hi _ hj hij => hf h hi hj hij
-/
theorem MonovaryOn.comp_antitone_on_left (h : MonovaryOn f g s) (hf : Antitone f') :
AntivaryOn (f' ∘ f) g s := fun _ hi _ hj hij => hf h hi hj hij

/--
theorem `AntivaryOn.comp_monotone_on_left` / 定理 `AntivaryOn.comp_monotone_on_left`

English:
theorem AntivaryOn.comp_monotone_on_left
  given: (h : AntivaryOn f g s) (hf : Monotone f')
  proof: fun _ hi _ hj hij => hf h hi hj hij

中文:
定理 AntivaryOn.comp_monotone_on_left
  条件: (h : AntivaryOn f g s) (hf : Monotone f')
  证明: fun _ hi _ hj hij => hf h hi hj hij
-/
theorem AntivaryOn.comp_monotone_on_left (h : AntivaryOn f g s) (hf : Monotone f') :
AntivaryOn (f' ∘ f) g s := fun _ hi _ hj hij => hf h hi hj hij

/--
theorem `AntivaryOn.comp_antitone_on_left` / 定理 `AntivaryOn.comp_antitone_on_left`

English:
theorem AntivaryOn.comp_antitone_on_left
  given: (h : AntivaryOn f g s) (hf : Antitone f')
  proof: fun _ hi _ hj hij => hf h hi hj hij

中文:
定理 AntivaryOn.comp_antitone_on_left
  条件: (h : AntivaryOn f g s) (hf : Antitone f')
  证明: fun _ hi _ hj hij => hf h hi hj hij
-/
theorem AntivaryOn.comp_antitone_on_left (h : AntivaryOn f g s) (hf : Antitone f') :
MonovaryOn (f' ∘ f) g s := fun _ hi _ hj hij => hf h hi hj hij

section OrderDual

open OrderDual

/--
theorem `Monovary.dual` / 定理 `Monovary.dual`

English:
theorem Monovary.dual
  statement: Monovary f g -> Monovary (toDual ∘ f) (toDual ∘ g)
  proof: swap

中文:
定理 Monovary.dual
  结论: Monovary f g -> Monovary (toDual ∘ f) (toDual ∘ g)
  证明: swap
-/
theorem Monovary.dual : Monovary f g -> Monovary (toDual ∘ f) (toDual ∘ g) :=
  swap

/--
theorem `Antivary.dual` / 定理 `Antivary.dual`

English:
theorem Antivary.dual
  statement: Antivary f g -> Antivary (toDual ∘ f) (toDual ∘ g)
  proof: swap

中文:
定理 Antivary.dual
  结论: Antivary f g -> Antivary (toDual ∘ f) (toDual ∘ g)
  证明: swap
-/
theorem Antivary.dual : Antivary f g -> Antivary (toDual ∘ f) (toDual ∘ g) :=
  swap

/--
theorem `Monovary.dual_left` / 定理 `Monovary.dual_left`

English:
theorem Monovary.dual_left
  statement: Monovary f g -> Antivary (toDual ∘ f) g
  proof: id

中文:
定理 Monovary.dual_left
  结论: Monovary f g -> Antivary (toDual ∘ f) g
  证明: id
-/
theorem Monovary.dual_left : Monovary f g -> Antivary (toDual ∘ f) g :=
  id

/--
theorem `Antivary.dual_left` / 定理 `Antivary.dual_left`

English:
theorem Antivary.dual_left
  statement: Antivary f g -> Monovary (toDual ∘ f) g
  proof: id

中文:
定理 Antivary.dual_left
  结论: Antivary f g -> Monovary (toDual ∘ f) g
  证明: id
-/
theorem Antivary.dual_left : Antivary f g -> Monovary (toDual ∘ f) g :=
  id

/--
theorem `Monovary.dual_right` / 定理 `Monovary.dual_right`

English:
theorem Monovary.dual_right
  statement: Monovary f g -> Antivary f (toDual ∘ g)
  proof: swap

中文:
定理 Monovary.dual_right
  结论: Monovary f g -> Antivary f (toDual ∘ g)
  证明: swap
-/
theorem Monovary.dual_right : Monovary f g -> Antivary f (toDual ∘ g) :=
  swap

/--
theorem `Antivary.dual_right` / 定理 `Antivary.dual_right`

English:
theorem Antivary.dual_right
  statement: Antivary f g -> Monovary f (toDual ∘ g)
  proof: swap

中文:
定理 Antivary.dual_right
  结论: Antivary f g -> Monovary f (toDual ∘ g)
  证明: swap
-/
theorem Antivary.dual_right : Antivary f g -> Monovary f (toDual ∘ g) :=
  swap

/--
theorem `MonovaryOn.dual` / 定理 `MonovaryOn.dual`

English:
theorem MonovaryOn.dual
  statement: MonovaryOn f g s -> MonovaryOn (toDual ∘ f) (toDual ∘ g) s
  proof: swap₂

中文:
定理 MonovaryOn.dual
  结论: MonovaryOn f g s -> MonovaryOn (toDual ∘ f) (toDual ∘ g) s
  证明: swap₂
-/
theorem MonovaryOn.dual : MonovaryOn f g s -> MonovaryOn (toDual ∘ f) (toDual ∘ g) s :=
  swap₂

/--
theorem `AntivaryOn.dual` / 定理 `AntivaryOn.dual`

English:
theorem AntivaryOn.dual
  statement: AntivaryOn f g s -> AntivaryOn (toDual ∘ f) (toDual ∘ g) s
  proof: swap₂

中文:
定理 AntivaryOn.dual
  结论: AntivaryOn f g s -> AntivaryOn (toDual ∘ f) (toDual ∘ g) s
  证明: swap₂
-/
theorem AntivaryOn.dual : AntivaryOn f g s -> AntivaryOn (toDual ∘ f) (toDual ∘ g) s :=
  swap₂

/--
theorem `MonovaryOn.dual_left` / 定理 `MonovaryOn.dual_left`

English:
theorem MonovaryOn.dual_left
  statement: MonovaryOn f g s -> AntivaryOn (toDual ∘ f) g s
  proof: id

中文:
定理 MonovaryOn.dual_left
  结论: MonovaryOn f g s -> AntivaryOn (toDual ∘ f) g s
  证明: id
-/
theorem MonovaryOn.dual_left : MonovaryOn f g s -> AntivaryOn (toDual ∘ f) g s :=
  id

/--
theorem `AntivaryOn.dual_left` / 定理 `AntivaryOn.dual_left`

English:
theorem AntivaryOn.dual_left
  statement: AntivaryOn f g s -> MonovaryOn (toDual ∘ f) g s
  proof: id

中文:
定理 AntivaryOn.dual_left
  结论: AntivaryOn f g s -> MonovaryOn (toDual ∘ f) g s
  证明: id
-/
theorem AntivaryOn.dual_left : AntivaryOn f g s -> MonovaryOn (toDual ∘ f) g s :=
  id

/--
theorem `MonovaryOn.dual_right` / 定理 `MonovaryOn.dual_right`

English:
theorem MonovaryOn.dual_right
  statement: MonovaryOn f g s -> AntivaryOn f (toDual ∘ g) s
  proof: swap₂

中文:
定理 MonovaryOn.dual_right
  结论: MonovaryOn f g s -> AntivaryOn f (toDual ∘ g) s
  证明: swap₂
-/
theorem MonovaryOn.dual_right : MonovaryOn f g s -> AntivaryOn f (toDual ∘ g) s :=
  swap₂

/--
theorem `AntivaryOn.dual_right` / 定理 `AntivaryOn.dual_right`

English:
theorem AntivaryOn.dual_right
  statement: AntivaryOn f g s -> MonovaryOn f (toDual ∘ g) s
  proof: swap₂

@[simp]

中文:
定理 AntivaryOn.dual_right
  结论: AntivaryOn f g s -> MonovaryOn f (toDual ∘ g) s
  证明: swap₂

@[simp]
-/
theorem AntivaryOn.dual_right : AntivaryOn f g s -> MonovaryOn f (toDual ∘ g) s :=
  swap₂

@[simp]
/--
theorem `monovary_toDual_left` / 定理 `monovary_toDual_left`

English:
theorem monovary_toDual_left
  statement: Monovary (toDual ∘ f) g ↔ Antivary f g
  proof: Iff.rfl

@[simp]

中文:
定理 monovary_toDual_left
  结论: Monovary (toDual ∘ f) g ↔ Antivary f g
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem monovary_toDual_left : Monovary (toDual ∘ f) g ↔ Antivary f g :=
  Iff.rfl

@[simp]
/--
theorem `monovary_toDual_right` / 定理 `monovary_toDual_right`

English:
theorem monovary_toDual_right
  statement: Monovary f (toDual ∘ g) ↔ Antivary f g
  proof: forall_comm

@[simp]

中文:
定理 monovary_toDual_right
  结论: Monovary f (toDual ∘ g) ↔ Antivary f g
  证明: forall_comm

@[simp]

Depends on / 依赖: forall_comm
-/
theorem monovary_toDual_right : Monovary f (toDual ∘ g) ↔ Antivary f g :=
  forall_comm

@[simp]
/--
theorem `antivary_toDual_left` / 定理 `antivary_toDual_left`

English:
theorem antivary_toDual_left
  statement: Antivary (toDual ∘ f) g ↔ Monovary f g
  proof: Iff.rfl

@[simp]

中文:
定理 antivary_toDual_left
  结论: Antivary (toDual ∘ f) g ↔ Monovary f g
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem antivary_toDual_left : Antivary (toDual ∘ f) g ↔ Monovary f g :=
  Iff.rfl

@[simp]
/--
theorem `antivary_toDual_right` / 定理 `antivary_toDual_right`

English:
theorem antivary_toDual_right
  statement: Antivary f (toDual ∘ g) ↔ Monovary f g
  proof: forall_comm

@[simp]

中文:
定理 antivary_toDual_right
  结论: Antivary f (toDual ∘ g) ↔ Monovary f g
  证明: forall_comm

@[simp]

Depends on / 依赖: forall_comm
-/
theorem antivary_toDual_right : Antivary f (toDual ∘ g) ↔ Monovary f g :=
  forall_comm

@[simp]
/--
theorem `monovaryOn_toDual_left` / 定理 `monovaryOn_toDual_left`

English:
theorem monovaryOn_toDual_left
  statement: MonovaryOn (toDual ∘ f) g s ↔ AntivaryOn f g s
  proof: Iff.rfl

@[simp]

中文:
定理 monovaryOn_toDual_left
  结论: MonovaryOn (toDual ∘ f) g s ↔ AntivaryOn f g s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem monovaryOn_toDual_left : MonovaryOn (toDual ∘ f) g s ↔ AntivaryOn f g s :=
  Iff.rfl

@[simp]
/--
theorem `monovaryOn_toDual_right` / 定理 `monovaryOn_toDual_right`

English:
theorem monovaryOn_toDual_right
  statement: MonovaryOn f (toDual ∘ g) s ↔ AntivaryOn f g s
  proof: forall₂_comm

@[simp]

中文:
定理 monovaryOn_toDual_right
  结论: MonovaryOn f (toDual ∘ g) s ↔ AntivaryOn f g s
  证明: forall₂_comm

@[simp]
-/
theorem monovaryOn_toDual_right : MonovaryOn f (toDual ∘ g) s ↔ AntivaryOn f g s :=
  forall₂_comm

@[simp]
/--
theorem `antivaryOn_toDual_left` / 定理 `antivaryOn_toDual_left`

English:
theorem antivaryOn_toDual_left
  statement: AntivaryOn (toDual ∘ f) g s ↔ MonovaryOn f g s
  proof: Iff.rfl

@[simp]

中文:
定理 antivaryOn_toDual_left
  结论: AntivaryOn (toDual ∘ f) g s ↔ MonovaryOn f g s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem antivaryOn_toDual_left : AntivaryOn (toDual ∘ f) g s ↔ MonovaryOn f g s :=
  Iff.rfl

@[simp]
/--
theorem `antivaryOn_toDual_right` / 定理 `antivaryOn_toDual_right`

English:
theorem antivaryOn_toDual_right
  statement: AntivaryOn f (toDual ∘ g) s ↔ MonovaryOn f g s
  proof: forall₂_comm

中文:
定理 antivaryOn_toDual_right
  结论: AntivaryOn f (toDual ∘ g) s ↔ MonovaryOn f g s
  证明: forall₂_comm
-/
theorem antivaryOn_toDual_right : AntivaryOn f (toDual ∘ g) s ↔ MonovaryOn f g s :=
  forall₂_comm

end OrderDual

section PartialOrder

variable [PartialOrder ι]

@[simp]
/--
theorem `monovary_id_iff` / 定理 `monovary_id_iff`

English:
theorem monovary_id_iff
  statement: Monovary f id ↔ Monotone f
  proof: monotone_iff_forall_lt.symm

@[simp]

中文:
定理 monovary_id_iff
  结论: Monovary f id ↔ Monotone f
  证明: monotone_iff_forall_lt.symm

@[simp]

Depends on / 依赖: monotone_iff_forall_lt, monotone_iff_forall_lt.symm
-/
theorem monovary_id_iff : Monovary f id ↔ Monotone f :=
  monotone_iff_forall_lt.symm

@[simp]
/--
theorem `antivary_id_iff` / 定理 `antivary_id_iff`

English:
theorem antivary_id_iff
  statement: Antivary f id ↔ Antitone f
  proof: antitone_iff_forall_lt.symm

@[simp]

中文:
定理 antivary_id_iff
  结论: Antivary f id ↔ Antitone f
  证明: antitone_iff_forall_lt.symm

@[simp]

Depends on / 依赖: antitone_iff_forall_lt, antitone_iff_forall_lt.symm
-/
theorem antivary_id_iff : Antivary f id ↔ Antitone f :=
  antitone_iff_forall_lt.symm

@[simp]
/--
theorem `monovaryOn_id_iff` / 定理 `monovaryOn_id_iff`

English:
theorem monovaryOn_id_iff
  statement: MonovaryOn f id s ↔ MonotoneOn f s
  proof: monotoneOn_iff_forall_lt.symm

@[simp]

中文:
定理 monovaryOn_id_iff
  结论: MonovaryOn f id s ↔ MonotoneOn f s
  证明: monotoneOn_iff_forall_lt.symm

@[simp]

Depends on / 依赖: monotoneOn_iff_forall_lt, monotoneOn_iff_forall_lt.symm
-/
theorem monovaryOn_id_iff : MonovaryOn f id s ↔ MonotoneOn f s :=
  monotoneOn_iff_forall_lt.symm

@[simp]
/--
theorem `antivaryOn_id_iff` / 定理 `antivaryOn_id_iff`

English:
theorem antivaryOn_id_iff
  statement: AntivaryOn f id s ↔ AntitoneOn f s
  proof: antitoneOn_iff_forall_lt.symm

中文:
定理 antivaryOn_id_iff
  结论: AntivaryOn f id s ↔ AntitoneOn f s
  证明: antitoneOn_iff_forall_lt.symm

Depends on / 依赖: antitoneOn_iff_forall_lt, antitoneOn_iff_forall_lt.symm
-/
theorem antivaryOn_id_iff : AntivaryOn f id s ↔ AntitoneOn f s :=
  antitoneOn_iff_forall_lt.symm

/--
lemma `StrictMono.trans_monovary` / 引理 `StrictMono.trans_monovary`

English:
lemma StrictMono.trans_monovary
  given: (hf : StrictMono f) (h : Monovary g f)
  statement: Monotone g
  proof: monotone_iff_forall_lt.2 fun _a _b hab => h hf hab

中文:
引理 StrictMono.trans_monovary
  条件: (hf : StrictMono f) (h : Monovary g f)
  结论: Monotone g
  证明: monotone_iff_forall_lt.2 fun _a _b hab => h hf hab

Depends on / 依赖: monotone_iff_forall_lt
-/
lemma StrictMono.trans_monovary (hf : StrictMono f) (h : Monovary g f) : Monotone g :=
monotone_iff_forall_lt.2 fun _a _b hab => h hf hab

/--
lemma `StrictMono.trans_antivary` / 引理 `StrictMono.trans_antivary`

English:
lemma StrictMono.trans_antivary
  given: (hf : StrictMono f) (h : Antivary g f)
  statement: Antitone g
  proof: antitone_iff_forall_lt.2 fun _a _b hab => h hf hab

中文:
引理 StrictMono.trans_antivary
  条件: (hf : StrictMono f) (h : Antivary g f)
  结论: Antitone g
  证明: antitone_iff_forall_lt.2 fun _a _b hab => h hf hab

Depends on / 依赖: antitone_iff_forall_lt
-/
lemma StrictMono.trans_antivary (hf : StrictMono f) (h : Antivary g f) : Antitone g :=
antitone_iff_forall_lt.2 fun _a _b hab => h hf hab

/--
lemma `StrictAnti.trans_monovary` / 引理 `StrictAnti.trans_monovary`

English:
lemma StrictAnti.trans_monovary
  given: (hf : StrictAnti f) (h : Monovary g f)
  statement: Antitone g
  proof: antitone_iff_forall_lt.2 fun _a _b hab => h hf hab

中文:
引理 StrictAnti.trans_monovary
  条件: (hf : StrictAnti f) (h : Monovary g f)
  结论: Antitone g
  证明: antitone_iff_forall_lt.2 fun _a _b hab => h hf hab

Depends on / 依赖: antitone_iff_forall_lt
-/
lemma StrictAnti.trans_monovary (hf : StrictAnti f) (h : Monovary g f) : Antitone g :=
antitone_iff_forall_lt.2 fun _a _b hab => h hf hab

/--
lemma `StrictAnti.trans_antivary` / 引理 `StrictAnti.trans_antivary`

English:
lemma StrictAnti.trans_antivary
  given: (hf : StrictAnti f) (h : Antivary g f)
  statement: Monotone g
  proof: monotone_iff_forall_lt.2 fun _a _b hab => h hf hab

中文:
引理 StrictAnti.trans_antivary
  条件: (hf : StrictAnti f) (h : Antivary g f)
  结论: Monotone g
  证明: monotone_iff_forall_lt.2 fun _a _b hab => h hf hab

Depends on / 依赖: monotone_iff_forall_lt
-/
lemma StrictAnti.trans_antivary (hf : StrictAnti f) (h : Antivary g f) : Monotone g :=
monotone_iff_forall_lt.2 fun _a _b hab => h hf hab

/--
lemma `StrictMonoOn.trans_monovaryOn` / 引理 `StrictMonoOn.trans_monovaryOn`

English:
lemma StrictMonoOn.trans_monovaryOn
  given: (hf : StrictMonoOn f s) (h : MonovaryOn g f s)
  proof: monotoneOn_iff_forall_lt.2 fun _a ha _b hb hab => h ha hb hf ha hb hab

中文:
引理 StrictMonoOn.trans_monovaryOn
  条件: (hf : StrictMonoOn f s) (h : MonovaryOn g f s)
  证明: monotoneOn_iff_forall_lt.2 fun _a ha _b hb hab => h ha hb hf ha hb hab

Depends on / 依赖: monotoneOn_iff_forall_lt
-/
lemma StrictMonoOn.trans_monovaryOn (hf : StrictMonoOn f s) (h : MonovaryOn g f s) :
MonotoneOn g s := monotoneOn_iff_forall_lt.2 fun _a ha _b hb hab => h ha hb hf ha hb hab

/--
lemma `StrictMonoOn.trans_antivaryOn` / 引理 `StrictMonoOn.trans_antivaryOn`

English:
lemma StrictMonoOn.trans_antivaryOn
  given: (hf : StrictMonoOn f s) (h : AntivaryOn g f s)
  proof: antitoneOn_iff_forall_lt.2 fun _a ha _b hb hab => h ha hb hf ha hb hab

中文:
引理 StrictMonoOn.trans_antivaryOn
  条件: (hf : StrictMonoOn f s) (h : AntivaryOn g f s)
  证明: antitoneOn_iff_forall_lt.2 fun _a ha _b hb hab => h ha hb hf ha hb hab

Depends on / 依赖: antitoneOn_iff_forall_lt
-/
lemma StrictMonoOn.trans_antivaryOn (hf : StrictMonoOn f s) (h : AntivaryOn g f s) :
AntitoneOn g s := antitoneOn_iff_forall_lt.2 fun _a ha _b hb hab => h ha hb hf ha hb hab

/--
lemma `StrictAntiOn.trans_monovaryOn` / 引理 `StrictAntiOn.trans_monovaryOn`

English:
lemma StrictAntiOn.trans_monovaryOn
  given: (hf : StrictAntiOn f s) (h : MonovaryOn g f s)
  proof: antitoneOn_iff_forall_lt.2 fun _a ha _b hb hab => h hb ha hf ha hb hab

中文:
引理 StrictAntiOn.trans_monovaryOn
  条件: (hf : StrictAntiOn f s) (h : MonovaryOn g f s)
  证明: antitoneOn_iff_forall_lt.2 fun _a ha _b hb hab => h hb ha hf ha hb hab

Depends on / 依赖: antitoneOn_iff_forall_lt
-/
lemma StrictAntiOn.trans_monovaryOn (hf : StrictAntiOn f s) (h : MonovaryOn g f s) :
AntitoneOn g s := antitoneOn_iff_forall_lt.2 fun _a ha _b hb hab => h hb ha hf ha hb hab

/--
lemma `StrictAntiOn.trans_antivaryOn` / 引理 `StrictAntiOn.trans_antivaryOn`

English:
lemma StrictAntiOn.trans_antivaryOn
  given: (hf : StrictAntiOn f s) (h : AntivaryOn g f s)
  proof: monotoneOn_iff_forall_lt.2 fun _a ha _b hb hab => h hb ha hf ha hb hab

中文:
引理 StrictAntiOn.trans_antivaryOn
  条件: (hf : StrictAntiOn f s) (h : AntivaryOn g f s)
  证明: monotoneOn_iff_forall_lt.2 fun _a ha _b hb hab => h hb ha hf ha hb hab

Depends on / 依赖: monotoneOn_iff_forall_lt
-/
lemma StrictAntiOn.trans_antivaryOn (hf : StrictAntiOn f s) (h : AntivaryOn g f s) :
MonotoneOn g s := monotoneOn_iff_forall_lt.2 fun _a ha _b hb hab => h hb ha hf ha hb hab

end PartialOrder

variable [LinearOrder ι]

/--
theorem `Monotone.monovary` / 定理 `Monotone.monovary`

English:
theorem Monotone.monovary
  given: (hf : Monotone f) (hg : Monotone g)
  statement: Monovary f g
  proof: fun _ _ hij => hf (hg.reflect_lt hij).le

中文:
定理 Monotone.monovary
  条件: (hf : Monotone f) (hg : Monotone g)
  结论: Monovary f g
  证明: fun _ _ hij => hf (hg.reflect_lt hij).le
-/
protected theorem Monotone.monovary (hf : Monotone f) (hg : Monotone g) : Monovary f g :=
  fun _ _ hij => hf (hg.reflect_lt hij).le

/--
theorem `Monotone.antivary` / 定理 `Monotone.antivary`

English:
theorem Monotone.antivary
  given: (hf : Monotone f) (hg : Antitone g)
  statement: Antivary f g
  proof: (hf.monovary hg.dual_right).dual_right

中文:
定理 Monotone.antivary
  条件: (hf : Monotone f) (hg : Antitone g)
  结论: Antivary f g
  证明: (hf.monovary hg.dual_right).dual_right
-/
protected theorem Monotone.antivary (hf : Monotone f) (hg : Antitone g) : Antivary f g :=
  (hf.monovary hg.dual_right).dual_right

/--
theorem `Antitone.monovary` / 定理 `Antitone.monovary`

English:
theorem Antitone.monovary
  given: (hf : Antitone f) (hg : Antitone g)
  statement: Monovary f g
  proof: (hf.dual_right.antivary hg).dual_left

中文:
定理 Antitone.monovary
  条件: (hf : Antitone f) (hg : Antitone g)
  结论: Monovary f g
  证明: (hf.dual_right.antivary hg).dual_left
-/
protected theorem Antitone.monovary (hf : Antitone f) (hg : Antitone g) : Monovary f g :=
  (hf.dual_right.antivary hg).dual_left

/--
theorem `Antitone.antivary` / 定理 `Antitone.antivary`

English:
theorem Antitone.antivary
  given: (hf : Antitone f) (hg : Monotone g)
  statement: Antivary f g
  proof: (hf.monovary hg.dual_right).dual_right

中文:
定理 Antitone.antivary
  条件: (hf : Antitone f) (hg : Monotone g)
  结论: Antivary f g
  证明: (hf.monovary hg.dual_right).dual_right
-/
protected theorem Antitone.antivary (hf : Antitone f) (hg : Monotone g) : Antivary f g :=
  (hf.monovary hg.dual_right).dual_right

/--
theorem `MonotoneOn.monovaryOn` / 定理 `MonotoneOn.monovaryOn`

English:
theorem MonotoneOn.monovaryOn
  given: (hf : MonotoneOn f s) (hg : MonotoneOn g s)
  proof: fun _ hi _ hj hij => hf hi hj (hg.reflect_lt hi hj hij).le

中文:
定理 MonotoneOn.monovaryOn
  条件: (hf : MonotoneOn f s) (hg : MonotoneOn g s)
  证明: fun _ hi _ hj hij => hf hi hj (hg.reflect_lt hi hj hij).le
-/
protected theorem MonotoneOn.monovaryOn (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonovaryOn f g s := fun _ hi _ hj hij => hf hi hj (hg.reflect_lt hi hj hij).le

/--
theorem `MonotoneOn.antivaryOn` / 定理 `MonotoneOn.antivaryOn`

English:
theorem MonotoneOn.antivaryOn
  given: (hf : MonotoneOn f s) (hg : AntitoneOn g s)
  proof: (hf.monovaryOn hg.dual_right).dual_right

中文:
定理 MonotoneOn.antivaryOn
  条件: (hf : MonotoneOn f s) (hg : AntitoneOn g s)
  证明: (hf.monovaryOn hg.dual_right).dual_right
-/
protected theorem MonotoneOn.antivaryOn (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntivaryOn f g s :=
  (hf.monovaryOn hg.dual_right).dual_right

/--
theorem `AntitoneOn.monovaryOn` / 定理 `AntitoneOn.monovaryOn`

English:
theorem AntitoneOn.monovaryOn
  given: (hf : AntitoneOn f s) (hg : AntitoneOn g s)
  proof: (hf.dual_right.antivaryOn hg).dual_left

中文:
定理 AntitoneOn.monovaryOn
  条件: (hf : AntitoneOn f s) (hg : AntitoneOn g s)
  证明: (hf.dual_right.antivaryOn hg).dual_left
-/
protected theorem AntitoneOn.monovaryOn (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    MonovaryOn f g s :=
  (hf.dual_right.antivaryOn hg).dual_left

/--
theorem `AntitoneOn.antivaryOn` / 定理 `AntitoneOn.antivaryOn`

English:
theorem AntitoneOn.antivaryOn
  given: (hf : AntitoneOn f s) (hg : MonotoneOn g s)
  proof: (hf.monovaryOn hg.dual_right).dual_right

中文:
定理 AntitoneOn.antivaryOn
  条件: (hf : AntitoneOn f s) (hg : MonotoneOn g s)
  证明: (hf.monovaryOn hg.dual_right).dual_right
-/
protected theorem AntitoneOn.antivaryOn (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    AntivaryOn f g s :=
  (hf.monovaryOn hg.dual_right).dual_right

end Preorder

section LinearOrder

variable [Preorder α] [LinearOrder β] [Preorder γ] {f : ι -> α} {g : ι -> β} {g' : β -> γ}
  {s : Set ι}

/--
theorem `MonovaryOn.comp_monotoneOn_right` / 定理 `MonovaryOn.comp_monotoneOn_right`

English:
theorem MonovaryOn.comp_monotoneOn_right
  given: (h : MonovaryOn f g s) (hg : MonotoneOn g' (g '' s))
  proof: fun _ hi _ hj hij =>
h hi hj hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij

中文:
定理 MonovaryOn.comp_monotoneOn_right
  条件: (h : MonovaryOn f g s) (hg : MonotoneOn g' (g '' s))
  证明: fun _ hi _ hj hij =>
h hi hj hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
-/
theorem MonovaryOn.comp_monotoneOn_right (h : MonovaryOn f g s) (hg : MonotoneOn g' (g '' s)) :
    MonovaryOn f (g' ∘ g) s := fun _ hi _ hj hij =>
h hi hj hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij

/--
theorem `MonovaryOn.comp_antitoneOn_right` / 定理 `MonovaryOn.comp_antitoneOn_right`

English:
theorem MonovaryOn.comp_antitoneOn_right
  given: (h : MonovaryOn f g s) (hg : AntitoneOn g' (g '' s))
  proof: fun _ hi _ hj hij =>
h hj hi hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij

中文:
定理 MonovaryOn.comp_antitoneOn_right
  条件: (h : MonovaryOn f g s) (hg : AntitoneOn g' (g '' s))
  证明: fun _ hi _ hj hij =>
h hj hi hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
-/
theorem MonovaryOn.comp_antitoneOn_right (h : MonovaryOn f g s) (hg : AntitoneOn g' (g '' s)) :
    AntivaryOn f (g' ∘ g) s := fun _ hi _ hj hij =>
h hj hi hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij

/--
theorem `AntivaryOn.comp_monotoneOn_right` / 定理 `AntivaryOn.comp_monotoneOn_right`

English:
theorem AntivaryOn.comp_monotoneOn_right
  given: (h : AntivaryOn f g s) (hg : MonotoneOn g' (g '' s))
  proof: fun _ hi _ hj hij =>
h hi hj hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij

中文:
定理 AntivaryOn.comp_monotoneOn_right
  条件: (h : AntivaryOn f g s) (hg : MonotoneOn g' (g '' s))
  证明: fun _ hi _ hj hij =>
h hi hj hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
-/
theorem AntivaryOn.comp_monotoneOn_right (h : AntivaryOn f g s) (hg : MonotoneOn g' (g '' s)) :
    AntivaryOn f (g' ∘ g) s := fun _ hi _ hj hij =>
h hi hj hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij

/--
theorem `AntivaryOn.comp_antitoneOn_right` / 定理 `AntivaryOn.comp_antitoneOn_right`

English:
theorem AntivaryOn.comp_antitoneOn_right
  given: (h : AntivaryOn f g s) (hg : AntitoneOn g' (g '' s))
  proof: fun _ hi _ hj hij =>
h hj hi hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij

@[symm]

中文:
定理 AntivaryOn.comp_antitoneOn_right
  条件: (h : AntivaryOn f g s) (hg : AntitoneOn g' (g '' s))
  证明: fun _ hi _ hj hij =>
h hj hi hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij

@[symm]
-/
theorem AntivaryOn.comp_antitoneOn_right (h : AntivaryOn f g s) (hg : AntitoneOn g' (g '' s)) :
    MonovaryOn f (g' ∘ g) s := fun _ hi _ hj hij =>
h hj hi hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij

@[symm]
/--
theorem `Monovary.symm` / 定理 `Monovary.symm`

English:
theorem Monovary.symm
  given: (h : Monovary f g)
  statement: Monovary g f
  proof: fun _ _ hf =>
le_of_not_gt fun hg => hf.not_ge h hg

@[symm]

中文:
定理 Monovary.symm
  条件: (h : Monovary f g)
  结论: Monovary g f
  证明: fun _ _ hf =>
le_of_not_gt fun hg => hf.not_ge h hg

@[symm]
-/
protected theorem Monovary.symm (h : Monovary f g) : Monovary g f := fun _ _ hf =>
le_of_not_gt fun hg => hf.not_ge h hg

@[symm]
/--
theorem `Antivary.symm` / 定理 `Antivary.symm`

English:
theorem Antivary.symm
  given: (h : Antivary f g)
  statement: Antivary g f
  proof: fun _ _ hf =>
le_of_not_gt fun hg => hf.not_ge h hg

@[symm]

中文:
定理 Antivary.symm
  条件: (h : Antivary f g)
  结论: Antivary g f
  证明: fun _ _ hf =>
le_of_not_gt fun hg => hf.not_ge h hg

@[symm]
-/
protected theorem Antivary.symm (h : Antivary f g) : Antivary g f := fun _ _ hf =>
le_of_not_gt fun hg => hf.not_ge h hg

@[symm]
/--
theorem `MonovaryOn.symm` / 定理 `MonovaryOn.symm`

English:
theorem MonovaryOn.symm
  given: (h : MonovaryOn f g s)
  statement: MonovaryOn g f s
  proof: fun _ hi _ hj hf =>
le_of_not_gt fun hg => hf.not_ge h hj hi hg

@[symm]

中文:
定理 MonovaryOn.symm
  条件: (h : MonovaryOn f g s)
  结论: MonovaryOn g f s
  证明: fun _ hi _ hj hf =>
le_of_not_gt fun hg => hf.not_ge h hj hi hg

@[symm]
-/
protected theorem MonovaryOn.symm (h : MonovaryOn f g s) : MonovaryOn g f s := fun _ hi _ hj hf =>
le_of_not_gt fun hg => hf.not_ge h hj hi hg

@[symm]
/--
theorem `AntivaryOn.symm` / 定理 `AntivaryOn.symm`

English:
theorem AntivaryOn.symm
  given: (h : AntivaryOn f g s)
  statement: AntivaryOn g f s
  proof: fun _ hi _ hj hf =>
le_of_not_gt fun hg => hf.not_ge h hi hj hg

中文:
定理 AntivaryOn.symm
  条件: (h : AntivaryOn f g s)
  结论: AntivaryOn g f s
  证明: fun _ hi _ hj hf =>
le_of_not_gt fun hg => hf.not_ge h hi hj hg
-/
protected theorem AntivaryOn.symm (h : AntivaryOn f g s) : AntivaryOn g f s := fun _ hi _ hj hf =>
le_of_not_gt fun hg => hf.not_ge h hi hj hg

end LinearOrder

section LinearOrder

variable [LinearOrder α] [LinearOrder β] {f : ι -> α} {g : ι -> β} {s : Set ι}

/--
theorem `monovary_comm` / 定理 `monovary_comm`

English:
theorem monovary_comm
  statement: Monovary f g ↔ Monovary g f
  proof: ⟨Monovary.symm, Monovary.symm⟩

中文:
定理 monovary_comm
  结论: Monovary f g ↔ Monovary g f
  证明: ⟨Monovary.symm, Monovary.symm⟩

Depends on / 依赖: Monovary, Monovary.symm
-/
theorem monovary_comm : Monovary f g ↔ Monovary g f :=
  ⟨Monovary.symm, Monovary.symm⟩

/--
theorem `antivary_comm` / 定理 `antivary_comm`

English:
theorem antivary_comm
  statement: Antivary f g ↔ Antivary g f
  proof: ⟨Antivary.symm, Antivary.symm⟩

中文:
定理 antivary_comm
  结论: Antivary f g ↔ Antivary g f
  证明: ⟨Antivary.symm, Antivary.symm⟩

Depends on / 依赖: Antivary, Antivary.symm
-/
theorem antivary_comm : Antivary f g ↔ Antivary g f :=
  ⟨Antivary.symm, Antivary.symm⟩

/--
theorem `monovaryOn_comm` / 定理 `monovaryOn_comm`

English:
theorem monovaryOn_comm
  statement: MonovaryOn f g s ↔ MonovaryOn g f s
  proof: ⟨MonovaryOn.symm, MonovaryOn.symm⟩

中文:
定理 monovaryOn_comm
  结论: MonovaryOn f g s ↔ MonovaryOn g f s
  证明: ⟨MonovaryOn.symm, MonovaryOn.symm⟩

Depends on / 依赖: MonovaryOn, MonovaryOn.symm
-/
theorem monovaryOn_comm : MonovaryOn f g s ↔ MonovaryOn g f s :=
  ⟨MonovaryOn.symm, MonovaryOn.symm⟩

/--
theorem `antivaryOn_comm` / 定理 `antivaryOn_comm`

English:
theorem antivaryOn_comm
  statement: AntivaryOn f g s ↔ AntivaryOn g f s
  proof: ⟨AntivaryOn.symm, AntivaryOn.symm⟩

中文:
定理 antivaryOn_comm
  结论: AntivaryOn f g s ↔ AntivaryOn g f s
  证明: ⟨AntivaryOn.symm, AntivaryOn.symm⟩

Depends on / 依赖: AntivaryOn, AntivaryOn.symm
-/
theorem antivaryOn_comm : AntivaryOn f g s ↔ AntivaryOn g f s :=
  ⟨AntivaryOn.symm, AntivaryOn.symm⟩

end LinearOrder
