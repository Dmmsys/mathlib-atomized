/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Function

/-!
# Piecewise functions

This file contains basic results on piecewise defined functions.
-/

public section

variable {α β γ δ : Type*} {ι : Sort*} {π : α -> Type*}

open Equiv Equiv.Perm Function

namespace Set

variable {δ : α -> Sort*} (s : Set α) (f g : forall i, δ i)

@[simp]
/--
theorem `piecewise_empty` / 定理 `piecewise_empty`

English:
theorem piecewise_empty
  given: [forall i : α, Decidable (i in (∅ : Set α))]
  statement: piecewise ∅ f g = g
  proof: by
  ext i
  simp [piecewise]

@[simp]

中文:
定理 piecewise_empty
  条件: [对任意 i : α, 可判定 (i in (∅ : 集合 α))]
  结论: piecewise ∅ f g = g
  证明: by
  ext i
  simp [piecewise]

@[simp]

Depends on / 依赖: piecewise
-/
theorem piecewise_empty [forall i : α, Decidable (i in (∅ : Set α))] : piecewise ∅ f g = g := by
  ext i
  simp [piecewise]

@[simp]
/--
theorem `piecewise_univ` / 定理 `piecewise_univ`

English:
theorem piecewise_univ
  given: [forall i : α, Decidable (i in (Set.univ : Set α))]
  proof: by
  ext i
  simp [piecewise]

中文:
定理 piecewise_univ
  条件: [对任意 i : α, 可判定 (i in (集合.univ : 集合 α))]
  证明: by
  ext i
  simp [piecewise]

Depends on / 依赖: piecewise
-/
theorem piecewise_univ [forall i : α, Decidable (i in (Set.univ : Set α))] :
    piecewise Set.univ f g = f := by
  ext i
  simp [piecewise]

/--
theorem `piecewise_insert_self` / 定理 `piecewise_insert_self`

English:
theorem piecewise_insert_self
  given: {j : α} [forall i, Decidable (i in insert j s)]
  proof: by simp [piecewise]

中文:
定理 piecewise_insert_self
  条件: {j : α} [对任意 i, 可判定 (i in insert j s)]
  证明: by simp [piecewise]

Depends on / 依赖: piecewise
-/
theorem piecewise_insert_self {j : α} [forall i, Decidable (i in insert j s)] :
    (insert j s).piecewise f g j = f j := by simp [piecewise]

variable [forall j, Decidable (j in s)]

/--
theorem `piecewise_insert` / 定理 `piecewise_insert`

English:
theorem piecewise_insert
  given: [DecidableEq α] (j : α) [forall i, Decidable (i in insert j s)]
  proof: by
  simp +unfoldPartialApp only [piecewise, mem_insert_iff]
  ext i
  by_cases h : i = j
  · rw [h]
    simp
  · by_cases h' : i in s <;> simp [h, h']

@[simp]

中文:
定理 piecewise_insert
  条件: [DecidableEq α] (j : α) [对任意 i, 可判定 (i in insert j s)]
  证明: by
  simp +unfoldPartialApp only [piecewise, mem_insert_iff]
  ext i
  by_cases h : i = j
  · rw [h]
    simp
  · by_cases h' : i in s <;> simp [h, h']

@[simp]

Depends on / 依赖: mem_insert_iff, piecewise, unfoldPartialApp
-/
theorem piecewise_insert [DecidableEq α] (j : α) [forall i, Decidable (i in insert j s)] :
    (insert j s).piecewise f g = Function.update (s.piecewise f g) j (f j) := by
  simp +unfoldPartialApp only [piecewise, mem_insert_iff]
  ext i
  by_cases h : i = j
  · rw [h]
    simp
  · by_cases h' : i in s <;> simp [h, h']

@[simp]
/--
theorem `piecewise_eq_of_mem` / 定理 `piecewise_eq_of_mem`

English:
theorem piecewise_eq_of_mem
  given: {i : α} (hi : i in s)
  statement: s.piecewise f g i = f i
  proof: if_pos hi

@[simp]

中文:
定理 piecewise_eq_of_mem
  条件: {i : α} (hi : i in s)
  结论: s.piecewise f g i = f i
  证明: if_pos hi

@[simp]

Depends on / 依赖: if_pos
-/
theorem piecewise_eq_of_mem {i : α} (hi : i in s) : s.piecewise f g i = f i :=
  if_pos hi

@[simp]
/--
theorem `piecewise_eq_of_notMem` / 定理 `piecewise_eq_of_notMem`

English:
theorem piecewise_eq_of_notMem
  given: {i : α} (hi : i ∉ s)
  statement: s.piecewise f g i = g i
  proof: if_neg hi

中文:
定理 piecewise_eq_of_notMem
  条件: {i : α} (hi : i ∉ s)
  结论: s.piecewise f g i = g i
  证明: if_neg hi

Depends on / 依赖: if_neg
-/
theorem piecewise_eq_of_notMem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i :=
  if_neg hi

/--
theorem `piecewise_singleton` / 定理 `piecewise_singleton`

English:
theorem piecewise_singleton
  statement: (x : α) [forall y, Decidable (y in ({x} : Set α))] [DecidableEq α]
  proof: by
  ext y
  by_cases hy : y = x
  · subst y
    simp
  · simp [hy]

中文:
定理 piecewise_singleton
  结论: (x : α) [对任意 y, 可判定 (y in ({x} : 集合 α))] [DecidableEq α]
  证明: by
  ext y
  by_cases hy : y = x
  · subst y
    simp
  · simp [hy]
-/
theorem piecewise_singleton (x : α) [forall y, Decidable (y in ({x} : Set α))] [DecidableEq α]
    (f g : α -> β) : piecewise {x} f g = Function.update g x (f x) := by
  ext y
  by_cases hy : y = x
  · subst y
    simp
  · simp [hy]

/--
theorem `piecewise_eqOn` / 定理 `piecewise_eqOn`

English:
theorem piecewise_eqOn
  given: (f g : α -> β)
  statement: EqOn (s.piecewise f g) f s
  proof: fun _ =>
  piecewise_eq_of_mem _ _ _

中文:
定理 piecewise_eqOn
  条件: (f g : α -> β)
  结论: EqOn (s.piecewise f g) f s
  证明: fun _ =>
  piecewise_eq_of_mem _ _ _
-/
theorem piecewise_eqOn (f g : α -> β) : EqOn (s.piecewise f g) f s := fun _ =>
  piecewise_eq_of_mem _ _ _

/--
theorem `piecewise_eqOn_compl` / 定理 `piecewise_eqOn_compl`

English:
theorem piecewise_eqOn_compl
  given: (f g : α -> β)
  statement: EqOn (s.piecewise f g) g sᶜ
  proof: fun _ =>
  piecewise_eq_of_notMem _ _ _

中文:
定理 piecewise_eqOn_compl
  条件: (f g : α -> β)
  结论: EqOn (s.piecewise f g) g sᶜ
  证明: fun _ =>
  piecewise_eq_of_notMem _ _ _
-/
theorem piecewise_eqOn_compl (f g : α -> β) : EqOn (s.piecewise f g) g sᶜ := fun _ =>
  piecewise_eq_of_notMem _ _ _

/--
theorem `piecewise_le` / 定理 `piecewise_le`

English:
theorem piecewise_le
  statement: {δ : α -> Type*} [forall i, Preorder (δ i)] {s : Set α} [forall j, Decidable (j in s)]
  proof: fun i => if h : i in s then by simp [*] else by simp [*]

中文:
定理 piecewise_le
  结论: {δ : α -> 类型} [对任意 i, 预序 (δ i)] {s : 集合 α} [对任意 j, 可判定 (j in s)]
  证明: fun i => if h : i in s then by simp [*] else by simp [*]
-/
theorem piecewise_le {δ : α -> Type*} [forall i, Preorder (δ i)] {s : Set α} [forall j, Decidable (j in s)]
    {f₁ f₂ g : forall i, δ i} (h₁ : forall i in s, f₁ i <= g i) (h₂ : forall i ∉ s, f₂ i <= g i) :
    s.piecewise f₁ f₂ <= g := fun i => if h : i in s then by simp [*] else by simp [*]

/--
theorem `le_piecewise` / 定理 `le_piecewise`

English:
theorem le_piecewise
  statement: {δ : α -> Type*} [forall i, Preorder (δ i)] {s : Set α} [forall j, Decidable (j in s)]
  proof: @piecewise_le α (fun i => (δ i)ᵒᵈ) _ s _ _ _ _ h₁ h₂

@[gcongr]

中文:
定理 le_piecewise
  结论: {δ : α -> 类型} [对任意 i, 预序 (δ i)] {s : 集合 α} [对任意 j, 可判定 (j in s)]
  证明: @piecewise_le α (fun i => (δ i)ᵒᵈ) _ s _ _ _ _ h₁ h₂

@[gcongr]

Depends on / 依赖: piecewise_le
-/
theorem le_piecewise {δ : α -> Type*} [forall i, Preorder (δ i)] {s : Set α} [forall j, Decidable (j in s)]
    {f₁ f₂ g : forall i, δ i} (h₁ : forall i in s, g i <= f₁ i) (h₂ : forall i ∉ s, g i <= f₂ i) :
    g <= s.piecewise f₁ f₂ :=
  @piecewise_le α (fun i => (δ i)ᵒᵈ) _ s _ _ _ _ h₁ h₂

@[gcongr]
/--
theorem `piecewise_mono` / 定理 `piecewise_mono`

English:
theorem piecewise_mono
  statement: {δ : α -> Type*} [forall i, Preorder (δ i)] {s : Set α}
  proof: by
  apply piecewise_le <;> intros <;> simp [*]

@[simp]

中文:
定理 piecewise_mono
  结论: {δ : α -> 类型} [对任意 i, 预序 (δ i)] {s : 集合 α}
  证明: by
  apply piecewise_le <;> intros <;> simp [*]

@[simp]

Depends on / 依赖: intros, piecewise_le
-/
theorem piecewise_mono {δ : α -> Type*} [forall i, Preorder (δ i)] {s : Set α}
    [forall j, Decidable (j in s)] {f₁ f₂ g₁ g₂ : forall i, δ i} (h₁ : forall i in s, f₁ i <= g₁ i)
    (h₂ : forall i ∉ s, f₂ i <= g₂ i) : s.piecewise f₁ f₂ <= s.piecewise g₁ g₂ := by
  apply piecewise_le <;> intros <;> simp [*]

@[simp]
/--
theorem `piecewise_insert_of_ne` / 定理 `piecewise_insert_of_ne`

English:
theorem piecewise_insert_of_ne
  given: {i j : α} (h : i != j) [forall i, Decidable (i in insert j s)]
  proof: by simp [piecewise, h]

@[simp]

中文:
定理 piecewise_insert_of_ne
  条件: {i j : α} (h : i != j) [对任意 i, 可判定 (i in insert j s)]
  证明: by simp [piecewise, h]

@[simp]

Depends on / 依赖: piecewise
-/
theorem piecewise_insert_of_ne {i j : α} (h : i != j) [forall i, Decidable (i in insert j s)] :
    (insert j s).piecewise f g i = s.piecewise f g i := by simp [piecewise, h]

@[simp]
/--
theorem `piecewise_compl` / 定理 `piecewise_compl`

English:
theorem piecewise_compl
  given: [forall i, Decidable (i in sᶜ)]
  statement: sᶜ.piecewise f g = s.piecewise g f
  proof: funext fun x => if hx : x in s then by simp [hx] else by simp [hx]

@[simp]

中文:
定理 piecewise_compl
  条件: [对任意 i, 可判定 (i in sᶜ)]
  结论: sᶜ.piecewise f g = s.piecewise g f
  证明: funext fun x => if hx : x in s then by simp [hx] else by simp [hx]

@[simp]
-/
theorem piecewise_compl [forall i, Decidable (i in sᶜ)] : sᶜ.piecewise f g = s.piecewise g f :=
  funext fun x => if hx : x in s then by simp [hx] else by simp [hx]

@[simp]
/--
theorem `piecewise_range_comp` / 定理 `piecewise_range_comp`

English:
theorem piecewise_range_comp
  statement: {ι : Sort*} (f : ι -> α) [forall j, Decidable (j in range f)]
  proof: (piecewise_eqOn ..).comp_eq

中文:
定理 piecewise_range_comp
  结论: {ι : 类型层*} (f : ι -> α) [对任意 j, 可判定 (j in range f)]
  证明: (piecewise_eqOn ..).comp_eq

Depends on / 依赖: comp_eq, piecewise_eqOn
-/
theorem piecewise_range_comp {ι : Sort*} (f : ι -> α) [forall j, Decidable (j in range f)]
    (g₁ g₂ : α -> β) : (range f).piecewise g₁ g₂ ∘ f = g₁ ∘ f :=
  (piecewise_eqOn ..).comp_eq

/--
lemma `piecewise_comp` / 引理 `piecewise_comp`

English:
lemma piecewise_comp
  given: (f g : α -> γ) (h : β -> α)
  proof: @instDecidablePredComp _ (· in s) _ h _;
    (s.piecewise f g) ∘ h = (h ⁻¹' s).piecewise (f ∘ h) (g ∘ h) := rfl

中文:
引理 piecewise_comp
  条件: (f g : α -> γ) (h : β -> α)
  证明: @instDecidablePredComp _ (· in s) _ h _;
    (s.piecewise f g) ∘ h = (h ⁻¹' s).piecewise (f ∘ h) (g ∘ h) := rfl

Depends on / 依赖: instDecidablePredComp
-/
lemma piecewise_comp (f g : α -> γ) (h : β -> α) :
    letI : DecidablePred (· in h ⁻¹' s) := @instDecidablePredComp _ (· in s) _ h _;
    (s.piecewise f g) ∘ h = (h ⁻¹' s).piecewise (f ∘ h) (g ∘ h) := rfl

/--
theorem `MapsTo.piecewise_ite` / 定理 `MapsTo.piecewise_ite`

English:
theorem MapsTo.piecewise_ite
  statement: {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {f₁ f₂ : α -> β}
  proof: by
  refine (h₁.congr ?_).union_union (h₂.congr ?_)
  exacts [(piecewise_eqOn s f₁ f₂).symm.mono inter_subset_right,
    (piecewise_eqOn_compl s f₁ f₂).symm.mono inter_subset_right]

中文:
定理 映射到.piecewise_ite
  结论: {s s₁ s₂ : 集合 α} {t t₁ t₂ : 集合 β} {f₁ f₂ : α -> β}
  证明: by
  refine (h₁.congr ?_).union_union (h₂.congr ?_)
  exacts [(piecewise_eqOn s f₁ f₂).symm.mono inter_subset_right,
    (piecewise_eqOn_compl s f₁ f₂).symm.mono inter_subset_right]

Depends on / 依赖: exacts, inter_subset_right, piecewise_eqOn, piecewise_eqOn_compl, symm.mono, union_union
-/
theorem MapsTo.piecewise_ite {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {f₁ f₂ : α -> β}
    [forall i, Decidable (i in s)] (h₁ : MapsTo f₁ (s₁ inter s) (t₁ inter t))
    (h₂ : MapsTo f₂ (s₂ inter sᶜ) (t₂ inter tᶜ)) :
    MapsTo (s.piecewise f₁ f₂) (s.ite s₁ s₂) (t.ite t₁ t₂) := by
  refine (h₁.congr ?_).union_union (h₂.congr ?_)
  exacts [(piecewise_eqOn s f₁ f₂).symm.mono inter_subset_right,
    (piecewise_eqOn_compl s f₁ f₂).symm.mono inter_subset_right]

/--
theorem `eqOn_piecewise` / 定理 `eqOn_piecewise`

English:
theorem eqOn_piecewise
  given: {f f' g : α -> β} {t}
  proof: by
  simp only [EqOn, ← forall_and]
  refine forall_congr' fun a => ?_; by_cases a in s <;> simp [*]

中文:
定理 eqOn_piecewise
  条件: {f f' g : α -> β} {t}
  证明: by
  simp only [EqOn, ← forall_and]
  refine forall_congr' fun a => ?_; by_cases a in s <;> simp [*]

Depends on / 依赖: forall_and, forall_congr
-/
theorem eqOn_piecewise {f f' g : α -> β} {t} :
    EqOn (s.piecewise f f') g t ↔ EqOn f g (t inter s) ∧ EqOn f' g (t inter sᶜ) := by
  simp only [EqOn, ← forall_and]
  refine forall_congr' fun a => ?_; by_cases a in s <;> simp [*]

/--
theorem `EqOn.piecewise_ite'` / 定理 `EqOn.piecewise_ite'`

English:
theorem EqOn.piecewise_ite'
  statement: {f f' g : α -> β} {t t'} (h : EqOn f g (t inter s))
  proof: by
  simp [eqOn_piecewise, *]

中文:
定理 EqOn.piecewise_ite'
  结论: {f f' g : α -> β} {t t'} (h : EqOn f g (t inter s))
  证明: by
  simp [eqOn_piecewise, *]

Depends on / 依赖: eqOn_piecewise
-/
theorem EqOn.piecewise_ite' {f f' g : α -> β} {t t'} (h : EqOn f g (t inter s))
    (h' : EqOn f' g (t' inter sᶜ)) : EqOn (s.piecewise f f') g (s.ite t t') := by
  simp [eqOn_piecewise, *]

/--
theorem `EqOn.piecewise_ite` / 定理 `EqOn.piecewise_ite`

English:
theorem EqOn.piecewise_ite
  given: {f f' g : α -> β} {t t'} (h : EqOn f g t) (h' : EqOn f' g t')
  proof: (h.mono inter_subset_left).piecewise_ite' s (h'.mono inter_subset_left)

中文:
定理 EqOn.piecewise_ite
  条件: {f f' g : α -> β} {t t'} (h : EqOn f g t) (h' : EqOn f' g t')
  证明: (h.mono inter_subset_left).piecewise_ite' s (h'.mono inter_subset_left)

Depends on / 依赖: h.mono, inter_subset_left, piecewise_ite
-/
theorem EqOn.piecewise_ite {f f' g : α -> β} {t t'} (h : EqOn f g t) (h' : EqOn f' g t') :
    EqOn (s.piecewise f f') g (s.ite t t') :=
  (h.mono inter_subset_left).piecewise_ite' s (h'.mono inter_subset_left)

/--
theorem `piecewise_preimage` / 定理 `piecewise_preimage`

English:
theorem piecewise_preimage
  given: (f g : α -> β) (t)
  statement: s.piecewise f g ⁻¹' t = s.ite (f ⁻¹' t) (g ⁻¹' t)
  proof: ext fun x => by by_cases x in s <;> simp [*, Set.ite]

中文:
定理 piecewise_preimage
  条件: (f g : α -> β) (t)
  结论: s.piecewise f g ⁻¹' t = s.ite (f ⁻¹' t) (g ⁻¹' t)
  证明: ext fun x => by by_cases x in s <;> simp [*, Set.ite]

Depends on / 依赖: Set.ite
-/
theorem piecewise_preimage (f g : α -> β) (t) : s.piecewise f g ⁻¹' t = s.ite (f ⁻¹' t) (g ⁻¹' t) :=
  ext fun x => by by_cases x in s <;> simp [*, Set.ite]

/--
theorem `apply_piecewise` / 定理 `apply_piecewise`

English:
theorem apply_piecewise
  given: {δ' : α -> Sort*} (h : forall i, δ i -> δ' i) {x : α}
  proof: by
  by_cases hx : x in s <;> simp [hx]

中文:
定理 apply_piecewise
  条件: {δ' : α -> 类型层*} (h : 对任意 i, δ i -> δ' i) {x : α}
  证明: by
  by_cases hx : x in s <;> simp [hx]
-/
theorem apply_piecewise {δ' : α -> Sort*} (h : forall i, δ i -> δ' i) {x : α} :
    h x (s.piecewise f g x) = s.piecewise (fun x => h x (f x)) (fun x => h x (g x)) x := by
  by_cases hx : x in s <;> simp [hx]

/--
theorem `apply_piecewise₂` / 定理 `apply_piecewise₂`

English:
theorem apply_piecewise₂
  statement: {δ' δ'' : α -> Sort*} (f' g' : forall i, δ' i) (h : forall i, δ i -> δ' i -> δ'' i)
  proof: by
  by_cases hx : x in s <;> simp [hx]

中文:
定理 apply_piecewise₂
  结论: {δ' δ'' : α -> 类型层*} (f' g' : 对任意 i, δ' i) (h : 对任意 i, δ i -> δ' i -> δ'' i)
  证明: by
  by_cases hx : x in s <;> simp [hx]
-/
theorem apply_piecewise₂ {δ' δ'' : α -> Sort*} (f' g' : forall i, δ' i) (h : forall i, δ i -> δ' i -> δ'' i)
    {x : α} :
    h x (s.piecewise f g x) (s.piecewise f' g' x) =
      s.piecewise (fun x => h x (f x) (f' x)) (fun x => h x (g x) (g' x)) x := by
  by_cases hx : x in s <;> simp [hx]

/--
theorem `piecewise_op` / 定理 `piecewise_op`

English:
theorem piecewise_op
  given: {δ' : α -> Sort*} (h : forall i, δ i -> δ' i)
  proof: funext fun _ => (apply_piecewise _ _ _ _).symm

中文:
定理 piecewise_op
  条件: {δ' : α -> 类型层*} (h : 对任意 i, δ i -> δ' i)
  证明: funext fun _ => (apply_piecewise _ _ _ _).symm

Depends on / 依赖: apply_piecewise
-/
theorem piecewise_op {δ' : α -> Sort*} (h : forall i, δ i -> δ' i) :
    (s.piecewise (fun x => h x (f x)) fun x => h x (g x)) = fun x => h x (s.piecewise f g x) :=
  funext fun _ => (apply_piecewise _ _ _ _).symm

/--
theorem `piecewise_op₂` / 定理 `piecewise_op₂`

English:
theorem piecewise_op₂
  given: {δ' δ'' : α -> Sort*} (f' g' : forall i, δ' i) (h : forall i, δ i -> δ' i -> δ'' i)
  proof: funext fun _ => (apply_piecewise₂ _ _ _ _ _ _).symm

@[simp]

中文:
定理 piecewise_op₂
  条件: {δ' δ'' : α -> 类型层*} (f' g' : 对任意 i, δ' i) (h : 对任意 i, δ i -> δ' i -> δ'' i)
  证明: funext fun _ => (apply_piecewise₂ _ _ _ _ _ _).symm

@[simp]
-/
theorem piecewise_op₂ {δ' δ'' : α -> Sort*} (f' g' : forall i, δ' i) (h : forall i, δ i -> δ' i -> δ'' i) :
    (s.piecewise (fun x => h x (f x) (f' x)) fun x => h x (g x) (g' x)) = fun x =>
      h x (s.piecewise f g x) (s.piecewise f' g' x) :=
  funext fun _ => (apply_piecewise₂ _ _ _ _ _ _).symm

@[simp]
/--
theorem `piecewise_same` / 定理 `piecewise_same`

English:
theorem piecewise_same
  statement: s.piecewise f f = f
  proof: by
  ext x
  by_cases hx : x in s <;> simp [hx]

中文:
定理 piecewise_same
  结论: s.piecewise f f = f
  证明: by
  ext x
  by_cases hx : x in s <;> simp [hx]
-/
theorem piecewise_same : s.piecewise f f = f := by
  ext x
  by_cases hx : x in s <;> simp [hx]

/--
theorem `range_piecewise` / 定理 `range_piecewise`

English:
theorem range_piecewise
  given: (f g : α -> β)
  statement: range (s.piecewise f g) = f '' s union g '' sᶜ
  proof: by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    by_cases h : x in s <;> [left; right] <;> use x <;> simp [h]
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> use x <;> simp_all

中文:
定理 range_piecewise
  条件: (f g : α -> β)
  结论: range (s.piecewise f g) = f '' s union g '' sᶜ
  证明: by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    by_cases h : x in s <;> [left; right] <;> use x <;> simp [h]
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> use x <;> simp_all
-/
theorem range_piecewise (f g : α -> β) : range (s.piecewise f g) = f '' s union g '' sᶜ := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    by_cases h : x in s <;> [left; right] <;> use x <;> simp [h]
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> use x <;> simp_all

/--
theorem `injective_piecewise_iff` / 定理 `injective_piecewise_iff`

English:
theorem injective_piecewise_iff
  given: {f g : α -> β}
  proof: by
  rw [← injOn_univ]; rw [← union_compl_self s]; rw [injOn_union (@disjoint_compl_right _ _ s)]; rw [(piecewise_eqOn s f g).injOn_iff]; rw [(piecewise_eqOn_compl s f g).injOn_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl <| forall₄_congr fun x hx y hy => ?_)
  rw [piecewise_eq_of_mem s f g hx]; rw [piecewise_eq_of_notMem s f g hy]

中文:
定理 injective_piecewise_iff
  条件: {f g : α -> β}
  证明: by
  rw [← injOn_univ]; rw [← union_compl_self s]; rw [injOn_union (@disjoint_compl_right _ _ s)]; rw [(piecewise_eqOn s f g).injOn_iff]; rw [(piecewise_eqOn_compl s f g).injOn_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl <| forall₄_congr fun x hx y hy => ?_)
  rw [piecewise_eq_of_mem s f g hx]; rw [piecewise_eq_of_notMem s f g hy]

Depends on / 依赖: Iff.rfl, and_congr, disjoint_compl_right, injOn_iff, injOn_union, injOn_univ, piecewise_eqOn, piecewise_eqOn_compl, piecewise_eq_of_mem, piecewise_eq_of_notMem, union_compl_self
-/
theorem injective_piecewise_iff {f g : α -> β} :
    Injective (s.piecewise f g) ↔
      InjOn f s ∧ InjOn g sᶜ ∧ forall x in s, forall y ∉ s, f x != g y := by
  rw [← injOn_univ]; rw [← union_compl_self s]; rw [injOn_union (@disjoint_compl_right _ _ s)]; rw [(piecewise_eqOn s f g).injOn_iff]; rw [(piecewise_eqOn_compl s f g).injOn_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl <| forall₄_congr fun x hx y hy => ?_)
  rw [piecewise_eq_of_mem s f g hx]; rw [piecewise_eq_of_notMem s f g hy]

/--
theorem `piecewise_mem_pi` / 定理 `piecewise_mem_pi`

English:
theorem piecewise_mem_pi
  statement: {δ : α -> Type*} {t : Set α} {t' : forall i, Set (δ i)} {f g} (hf : f in pi t t')
  proof: by
  intro i ht
  by_cases hs : i in s <;> simp [hf i ht, hg i ht, hs]

@[simp]

中文:
定理 piecewise_mem_pi
  结论: {δ : α -> 类型} {t : 集合 α} {t' : 对任意 i, 集合 (δ i)} {f g} (hf : f in pi t t')
  证明: by
  intro i ht
  by_cases hs : i in s <;> simp [hf i ht, hg i ht, hs]

@[simp]
-/
theorem piecewise_mem_pi {δ : α -> Type*} {t : Set α} {t' : forall i, Set (δ i)} {f g} (hf : f in pi t t')
    (hg : g in pi t t') : s.piecewise f g in pi t t' := by
  intro i ht
  by_cases hs : i in s <;> simp [hf i ht, hg i ht, hs]

@[simp]
/--
theorem `pi_piecewise` / 定理 `pi_piecewise`

English:
theorem pi_piecewise
  statement: {ι : Type*} {α : ι -> Type*} (s s' : Set ι) (t t' : forall i, Set (α i))
  proof: pi_if _ _ _

中文:
定理 pi_piecewise
  结论: {ι : 类型} {α : ι -> 类型} (s s' : 集合 ι) (t t' : 对任意 i, 集合 (α i))
  证明: pi_if _ _ _

Depends on / 依赖: pi_if
-/
theorem pi_piecewise {ι : Type*} {α : ι -> Type*} (s s' : Set ι) (t t' : forall i, Set (α i))
    [forall x, Decidable (x in s')] : pi s (s'.piecewise t t') = pi (s inter s') t inter pi (s \ s') t' :=
  pi_if _ _ _

/--
theorem `univ_pi_piecewise` / 定理 `univ_pi_piecewise`

English:
theorem univ_pi_piecewise
  statement: {ι : Type*} {α : ι -> Type*} (s : Set ι) (t t' : forall i, Set (α i))
  proof: by
  simp [compl_eq_univ_sdiff]

中文:
定理 univ_pi_piecewise
  结论: {ι : 类型} {α : ι -> 类型} (s : 集合 ι) (t t' : 对任意 i, 集合 (α i))
  证明: by
  simp [compl_eq_univ_sdiff]

Depends on / 依赖: compl_eq_univ_sdiff
-/
theorem univ_pi_piecewise {ι : Type*} {α : ι -> Type*} (s : Set ι) (t t' : forall i, Set (α i))
    [forall x, Decidable (x in s)] : pi univ (s.piecewise t t') = pi s t inter pi sᶜ t' := by
  simp [compl_eq_univ_sdiff]

/--
theorem `univ_pi_piecewise_univ` / 定理 `univ_pi_piecewise_univ`

English:
theorem univ_pi_piecewise_univ
  statement: {ι : Type*} {α : ι -> Type*} (s : Set ι) (t : forall i, Set (α i))
  proof: by simp

中文:
定理 univ_pi_piecewise_univ
  结论: {ι : 类型} {α : ι -> 类型} (s : 集合 ι) (t : 对任意 i, 集合 (α i))
  证明: by simp
-/
theorem univ_pi_piecewise_univ {ι : Type*} {α : ι -> Type*} (s : Set ι) (t : forall i, Set (α i))
    [forall x, Decidable (x in s)] : pi univ (s.piecewise t fun _ => univ) = pi s t := by simp

end Set
