/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Function

/-!
# Monotone functions over sets
-/

public section

variable {α β γ : Type*}

open Equiv Equiv.Perm Function

namespace Set


/-! ### Congruence lemmas for monotonicity and antitonicity -/
section Order

variable {s : Set α} {f₁ f₂ : α -> β} [Preorder α] [Preorder β]

/--
theorem `_root_.MonotoneOn.congr` / 定理 `_root_.MonotoneOn.congr`

English:
theorem _root_.MonotoneOn.congr
  given: (h₁ : MonotoneOn f₁ s) (h : s.EqOn f₁ f₂)
  statement: MonotoneOn f₂ s
  proof: by
  intro a ha b hb hab
  rw [← h ha]; rw [← h hb]
  exact h₁ ha hb hab

中文:
定理 _root_.MonotoneOn.congr
  条件: (h₁ : MonotoneOn f₁ s) (h : s.EqOn f₁ f₂)
  结论: MonotoneOn f₂ s
  证明: by
  intro a ha b hb hab
  rw [← h ha]; rw [← h hb]
  exact h₁ ha hb hab
-/
theorem _root_.MonotoneOn.congr (h₁ : MonotoneOn f₁ s) (h : s.EqOn f₁ f₂) : MonotoneOn f₂ s := by
  intro a ha b hb hab
  rw [← h ha]; rw [← h hb]
  exact h₁ ha hb hab

/--
theorem `_root_.AntitoneOn.congr` / 定理 `_root_.AntitoneOn.congr`

English:
theorem _root_.AntitoneOn.congr
  given: (h₁ : AntitoneOn f₁ s) (h : s.EqOn f₁ f₂)
  statement: AntitoneOn f₂ s
  proof: h₁.dual_right.congr h

中文:
定理 _root_.AntitoneOn.congr
  条件: (h₁ : AntitoneOn f₁ s) (h : s.EqOn f₁ f₂)
  结论: AntitoneOn f₂ s
  证明: h₁.dual_right.congr h

Depends on / 依赖: dual_right, dual_right.congr
-/
theorem _root_.AntitoneOn.congr (h₁ : AntitoneOn f₁ s) (h : s.EqOn f₁ f₂) : AntitoneOn f₂ s :=
  h₁.dual_right.congr h

/--
theorem `_root_.StrictMonoOn.congr` / 定理 `_root_.StrictMonoOn.congr`

English:
theorem _root_.StrictMonoOn.congr
  given: (h₁ : StrictMonoOn f₁ s) (h : s.EqOn f₁ f₂)
  proof: by
  intro a ha b hb hab
  rw [← h ha]; rw [← h hb]
  exact h₁ ha hb hab

中文:
定理 _root_.StrictMonoOn.congr
  条件: (h₁ : StrictMonoOn f₁ s) (h : s.EqOn f₁ f₂)
  证明: by
  intro a ha b hb hab
  rw [← h ha]; rw [← h hb]
  exact h₁ ha hb hab
-/
theorem _root_.StrictMonoOn.congr (h₁ : StrictMonoOn f₁ s) (h : s.EqOn f₁ f₂) :
    StrictMonoOn f₂ s := by
  intro a ha b hb hab
  rw [← h ha]; rw [← h hb]
  exact h₁ ha hb hab

/--
theorem `_root_.StrictAntiOn.congr` / 定理 `_root_.StrictAntiOn.congr`

English:
theorem _root_.StrictAntiOn.congr
  given: (h₁ : StrictAntiOn f₁ s) (h : s.EqOn f₁ f₂)
  statement: StrictAntiOn f₂ s
  proof: h₁.dual_right.congr h

中文:
定理 _root_.StrictAntiOn.congr
  条件: (h₁ : StrictAntiOn f₁ s) (h : s.EqOn f₁ f₂)
  结论: StrictAntiOn f₂ s
  证明: h₁.dual_right.congr h

Depends on / 依赖: dual_right, dual_right.congr
-/
theorem _root_.StrictAntiOn.congr (h₁ : StrictAntiOn f₁ s) (h : s.EqOn f₁ f₂) : StrictAntiOn f₂ s :=
  h₁.dual_right.congr h

/--
theorem `EqOn.congr_monotoneOn` / 定理 `EqOn.congr_monotoneOn`

English:
theorem EqOn.congr_monotoneOn
  given: (h : s.EqOn f₁ f₂)
  statement: MonotoneOn f₁ s ↔ MonotoneOn f₂ s
  proof: ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

中文:
定理 EqOn.congr_monotoneOn
  条件: (h : s.EqOn f₁ f₂)
  结论: MonotoneOn f₁ s ↔ MonotoneOn f₂ s
  证明: ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

Depends on / 依赖: h.symm
-/
theorem EqOn.congr_monotoneOn (h : s.EqOn f₁ f₂) : MonotoneOn f₁ s ↔ MonotoneOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

/--
theorem `EqOn.congr_antitoneOn` / 定理 `EqOn.congr_antitoneOn`

English:
theorem EqOn.congr_antitoneOn
  given: (h : s.EqOn f₁ f₂)
  statement: AntitoneOn f₁ s ↔ AntitoneOn f₂ s
  proof: ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

中文:
定理 EqOn.congr_antitoneOn
  条件: (h : s.EqOn f₁ f₂)
  结论: AntitoneOn f₁ s ↔ AntitoneOn f₂ s
  证明: ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

Depends on / 依赖: h.symm
-/
theorem EqOn.congr_antitoneOn (h : s.EqOn f₁ f₂) : AntitoneOn f₁ s ↔ AntitoneOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

/--
theorem `EqOn.congr_strictMonoOn` / 定理 `EqOn.congr_strictMonoOn`

English:
theorem EqOn.congr_strictMonoOn
  given: (h : s.EqOn f₁ f₂)
  statement: StrictMonoOn f₁ s ↔ StrictMonoOn f₂ s
  proof: ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

中文:
定理 EqOn.congr_strictMonoOn
  条件: (h : s.EqOn f₁ f₂)
  结论: StrictMonoOn f₁ s ↔ StrictMonoOn f₂ s
  证明: ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

Depends on / 依赖: h.symm
-/
theorem EqOn.congr_strictMonoOn (h : s.EqOn f₁ f₂) : StrictMonoOn f₁ s ↔ StrictMonoOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

/--
theorem `EqOn.congr_strictAntiOn` / 定理 `EqOn.congr_strictAntiOn`

English:
theorem EqOn.congr_strictAntiOn
  given: (h : s.EqOn f₁ f₂)
  statement: StrictAntiOn f₁ s ↔ StrictAntiOn f₂ s
  proof: ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

中文:
定理 EqOn.congr_strictAntiOn
  条件: (h : s.EqOn f₁ f₂)
  结论: StrictAntiOn f₁ s ↔ StrictAntiOn f₂ s
  证明: ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

Depends on / 依赖: h.symm
-/
theorem EqOn.congr_strictAntiOn (h : s.EqOn f₁ f₂) : StrictAntiOn f₁ s ↔ StrictAntiOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

end Order

/-! ### Monotonicity lemmas -/
section Mono

variable {s s₂ : Set α} {f : α -> β} [Preorder α] [Preorder β]

/--
theorem `_root_.MonotoneOn.mono` / 定理 `_root_.MonotoneOn.mono`

English:
theorem _root_.MonotoneOn.mono
  given: (h : MonotoneOn f s) (h' : s₂ subseteq s)
  statement: MonotoneOn f s₂
  proof: fun _ hx _ hy => h (h' hx) (h' hy)

中文:
定理 _root_.MonotoneOn.mono
  条件: (h : MonotoneOn f s) (h' : s₂ subseteq s)
  结论: MonotoneOn f s₂
  证明: fun _ hx _ hy => h (h' hx) (h' hy)
-/
theorem _root_.MonotoneOn.mono (h : MonotoneOn f s) (h' : s₂ subseteq s) : MonotoneOn f s₂ :=
  fun _ hx _ hy => h (h' hx) (h' hy)

/--
theorem `_root_.AntitoneOn.mono` / 定理 `_root_.AntitoneOn.mono`

English:
theorem _root_.AntitoneOn.mono
  given: (h : AntitoneOn f s) (h' : s₂ subseteq s)
  statement: AntitoneOn f s₂
  proof: fun _ hx _ hy => h (h' hx) (h' hy)

中文:
定理 _root_.AntitoneOn.mono
  条件: (h : AntitoneOn f s) (h' : s₂ subseteq s)
  结论: AntitoneOn f s₂
  证明: fun _ hx _ hy => h (h' hx) (h' hy)

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.emptyTo, emptyTo
-/
theorem _root_.AntitoneOn.mono (h : AntitoneOn f s) (h' : s₂ subseteq s) : AntitoneOn f s₂ :=
  fun _ hx _ hy => h (h' hx) (h' hy)

/--
theorem `_root_.StrictMonoOn.mono` / 定理 `_root_.StrictMonoOn.mono`

English:
theorem _root_.StrictMonoOn.mono
  given: (h : StrictMonoOn f s) (h' : s₂ subseteq s)
  statement: StrictMonoOn f s₂
  proof: fun _ hx _ hy => h (h' hx) (h' hy)

中文:
定理 _root_.StrictMonoOn.mono
  条件: (h : StrictMonoOn f s) (h' : s₂ subseteq s)
  结论: StrictMonoOn f s₂
  证明: fun _ hx _ hy => h (h' hx) (h' hy)
-/
theorem _root_.StrictMonoOn.mono (h : StrictMonoOn f s) (h' : s₂ subseteq s) : StrictMonoOn f s₂ :=
  fun _ hx _ hy => h (h' hx) (h' hy)

/--
theorem `_root_.StrictAntiOn.mono` / 定理 `_root_.StrictAntiOn.mono`

English:
theorem _root_.StrictAntiOn.mono
  given: (h : StrictAntiOn f s) (h' : s₂ subseteq s)
  statement: StrictAntiOn f s₂
  proof: fun _ hx _ hy => h (h' hx) (h' hy)

中文:
定理 _root_.StrictAntiOn.mono
  条件: (h : StrictAntiOn f s) (h' : s₂ subseteq s)
  结论: StrictAntiOn f s₂
  证明: fun _ hx _ hy => h (h' hx) (h' hy)
-/
theorem _root_.StrictAntiOn.mono (h : StrictAntiOn f s) (h' : s₂ subseteq s) : StrictAntiOn f s₂ :=
  fun _ hx _ hy => h (h' hx) (h' hy)

/--
theorem `_root_.MonotoneOn.monotone` / 定理 `_root_.MonotoneOn.monotone`

English:
theorem _root_.MonotoneOn.monotone
  given: (h : MonotoneOn f s)
  proof: fun x y hle => h x.coe_prop y.coe_prop hle

中文:
定理 _root_.MonotoneOn.monotone
  条件: (h : MonotoneOn f s)
  证明: fun x y hle => h x.coe_prop y.coe_prop hle
-/
protected theorem _root_.MonotoneOn.monotone (h : MonotoneOn f s) :
    Monotone (f ∘ Subtype.val : s -> β) :=
  fun x y hle => h x.coe_prop y.coe_prop hle

/--
theorem `_root_.AntitoneOn.monotone` / 定理 `_root_.AntitoneOn.monotone`

English:
theorem _root_.AntitoneOn.monotone
  given: (h : AntitoneOn f s)
  proof: fun x y hle => h x.coe_prop y.coe_prop hle

中文:
定理 _root_.AntitoneOn.monotone
  条件: (h : AntitoneOn f s)
  证明: fun x y hle => h x.coe_prop y.coe_prop hle
-/
protected theorem _root_.AntitoneOn.monotone (h : AntitoneOn f s) :
    Antitone (f ∘ Subtype.val : s -> β) :=
  fun x y hle => h x.coe_prop y.coe_prop hle

/--
theorem `_root_.StrictMonoOn.strictMono` / 定理 `_root_.StrictMonoOn.strictMono`

English:
theorem _root_.StrictMonoOn.strictMono
  given: (h : StrictMonoOn f s)
  proof: fun x y hlt => h x.coe_prop y.coe_prop hlt

中文:
定理 _root_.StrictMonoOn.strictMono
  条件: (h : StrictMonoOn f s)
  证明: fun x y hlt => h x.coe_prop y.coe_prop hlt
-/
protected theorem _root_.StrictMonoOn.strictMono (h : StrictMonoOn f s) :
    StrictMono (f ∘ Subtype.val : s -> β) :=
  fun x y hlt => h x.coe_prop y.coe_prop hlt

/--
theorem `_root_.StrictAntiOn.strictAnti` / 定理 `_root_.StrictAntiOn.strictAnti`

English:
theorem _root_.StrictAntiOn.strictAnti
  given: (h : StrictAntiOn f s)
  proof: fun x y hlt => h x.coe_prop y.coe_prop hlt

中文:
定理 _root_.StrictAntiOn.strictAnti
  条件: (h : StrictAntiOn f s)
  证明: fun x y hlt => h x.coe_prop y.coe_prop hlt
-/
protected theorem _root_.StrictAntiOn.strictAnti (h : StrictAntiOn f s) :
    StrictAnti (f ∘ Subtype.val : s -> β) :=
  fun x y hlt => h x.coe_prop y.coe_prop hlt

/--
lemma `monotoneOn_insert_iff` / 引理 `monotoneOn_insert_iff`

English:
lemma monotoneOn_insert_iff
  given: {a : α}
  proof: by
  simp [MonotoneOn, forall_and]

中文:
引理 monotoneOn_insert_iff
  条件: {a : α}
  证明: by
  simp [MonotoneOn, forall_and]

Depends on / 依赖: MonotoneOn, forall_and
-/
lemma monotoneOn_insert_iff {a : α} :
    MonotoneOn f (insert a s) ↔
      (forall b in s, b <= a -> f b <= f a) ∧ (forall b in s, a <= b -> f a <= f b) ∧ MonotoneOn f s := by
  simp [MonotoneOn, forall_and]

/--
lemma `antitoneOn_insert_iff` / 引理 `antitoneOn_insert_iff`

English:
lemma antitoneOn_insert_iff
  given: {a : α}
  proof: @monotoneOn_insert_iff α βᵒᵈ _ _ _ _ _

中文:
引理 antitoneOn_insert_iff
  条件: {a : α}
  证明: @monotoneOn_insert_iff α βᵒᵈ _ _ _ _ _

Depends on / 依赖: monotoneOn_insert_iff
-/
lemma antitoneOn_insert_iff {a : α} :
    AntitoneOn f (insert a s) ↔
      (forall b in s, b <= a -> f a <= f b) ∧ (forall b in s, a <= b -> f b <= f a) ∧ AntitoneOn f s :=
  @monotoneOn_insert_iff α βᵒᵈ _ _ _ _ _

end Mono

end Set



open Function

/-! ### Monotone -/
namespace Monotone

variable [Preorder α] [Preorder β] {f : α -> β}

/--
theorem `domRestrict` / 定理 `domRestrict`

English:
theorem domRestrict
  given: (h : Monotone f) (s : Set α)
  statement: Monotone (s.domRestrict f)
  proof: fun _ _ hxy => h hxy

@[deprecated (since := "2026-07-19")] alias restrict := Monotone.domRestrict

中文:
定理 domRestrict
  条件: (h : Monotone f) (s : Set α)
  结论: Monotone (s.domRestrict f)
  证明: fun _ _ hxy => h hxy

@[deprecated (since := "2026-07-19")] alias restrict := Monotone.domRestrict
-/
protected theorem domRestrict (h : Monotone f) (s : Set α) : Monotone (s.domRestrict f) :=
  fun _ _ hxy => h hxy

@[deprecated (since := "2026-07-19")] alias restrict := Monotone.domRestrict

/--
theorem `codRestrict` / 定理 `codRestrict`

English:
theorem codRestrict
  given: (h : Monotone f) {s : Set β} (hs : forall x, f x in s)
  proof: h

中文:
定理 codRestrict
  条件: (h : Monotone f) {s : Set β} (hs : 对任意 x, f x in s)
  证明: h
-/
protected theorem codRestrict (h : Monotone f) {s : Set β} (hs : forall x, f x in s) :
    Monotone (s.codRestrict f hs) :=
  h

/--
theorem `rangeFactorization` / 定理 `rangeFactorization`

English:
theorem rangeFactorization
  given: (h : Monotone f)
  statement: Monotone (Set.rangeFactorization f)
  proof: h

中文:
定理 rangeFactorization
  条件: (h : Monotone f)
  结论: Monotone (Set.rangeFactorization f)
  证明: h
-/
protected theorem rangeFactorization (h : Monotone f) : Monotone (Set.rangeFactorization f) :=
  h

end Monotone

section strictMono

variable [Preorder α] [Preorder β] {f : α -> β} {s : Set α}

@[simp]
/--
theorem `strictMono_domRestrict` / 定理 `strictMono_domRestrict`

English:
theorem strictMono_domRestrict
  statement: StrictMono (s.domRestrict f) ↔ StrictMonoOn f s
  proof: by
  simp [Set.domRestrict, StrictMono, StrictMonoOn]

alias ⟨_root_.StrictMono.of_domRestrict, _root_.StrictMonoOn.domRestrict⟩ := strictMono_domRestrict

@[deprecated (since := "2026-07-19")] alias strictMono_restrict := strictMono_domRestrict
@[deprecated (since := "2026-07-19")]
alias _root_.Str

中文:
定理 strictMono_domRestrict
  结论: StrictMono (s.domRestrict f) ↔ StrictMonoOn f s
  证明: by
  simp [Set.domRestrict, StrictMono, StrictMonoOn]

alias ⟨_root_.StrictMono.of_domRestrict, _root_.StrictMonoOn.domRestrict⟩ := strictMono_domRestrict

@[deprecated (since := "2026-07-19")] alias strictMono_restrict := strictMono_domRestrict
@[deprecated (since := "2026-07-19")]
alias _root_.Str

Depends on / 依赖: Set.domRestrict, StrictMono, StrictMonoOn, domRestrict
-/
theorem strictMono_domRestrict : StrictMono (s.domRestrict f) ↔ StrictMonoOn f s := by
  simp [Set.domRestrict, StrictMono, StrictMonoOn]

alias ⟨_root_.StrictMono.of_domRestrict, _root_.StrictMonoOn.domRestrict⟩ := strictMono_domRestrict

@[deprecated (since := "2026-07-19")] alias strictMono_restrict := strictMono_domRestrict
@[deprecated (since := "2026-07-19")]
alias _root_.StrictMono.of_restrict := _root_.StrictMono.of_domRestrict
@[deprecated (since := "2026-07-19")]
alias _root_.StrictMonoOn.restrict := _root_.StrictMonoOn.domRestrict

/--
theorem `StrictMono.codRestrict` / 定理 `StrictMono.codRestrict`

English:
theorem StrictMono.codRestrict
  statement: (hf : StrictMono f)
  proof: hf

中文:
定理 StrictMono.codRestrict
  结论: (hf : StrictMono f)
  证明: hf
-/
theorem StrictMono.codRestrict (hf : StrictMono f)
    {s : Set β} (hs : forall x, f x in s) : StrictMono (Set.codRestrict f s hs) :=
  hf

/--
lemma `strictMonoOn_insert_iff` / 引理 `strictMonoOn_insert_iff`

English:
lemma strictMonoOn_insert_iff
  given: {a : α}
  proof: by
  simp [StrictMonoOn, forall_and]

中文:
引理 strictMonoOn_insert_iff
  条件: {a : α}
  证明: by
  simp [StrictMonoOn, forall_and]

Depends on / 依赖: StrictMonoOn, forall_and
-/
lemma strictMonoOn_insert_iff {a : α} :
    StrictMonoOn f (insert a s) ↔
       (forall b in s, b < a -> f b < f a) ∧ (forall b in s, a < b -> f a < f b) ∧ StrictMonoOn f s := by
  simp [StrictMonoOn, forall_and]

/--
lemma `strictAntiOn_insert_iff` / 引理 `strictAntiOn_insert_iff`

English:
lemma strictAntiOn_insert_iff
  given: {a : α}
  proof: @strictMonoOn_insert_iff α βᵒᵈ _ _ _ _ _

中文:
引理 strictAntiOn_insert_iff
  条件: {a : α}
  证明: @strictMonoOn_insert_iff α βᵒᵈ _ _ _ _ _

Depends on / 依赖: strictMonoOn_insert_iff
-/
lemma strictAntiOn_insert_iff {a : α} :
    StrictAntiOn f (insert a s) ↔
       (forall b in s, b < a -> f a < f b) ∧ (forall b in s, a < b -> f b < f a) ∧ StrictAntiOn f s :=
  @strictMonoOn_insert_iff α βᵒᵈ _ _ _ _ _

/--
lemma `strictMonoOn_insert_iff_of_forall_le` / 引理 `strictMonoOn_insert_iff_of_forall_le`

English:
lemma strictMonoOn_insert_iff_of_forall_le
  given: {a : α} (ha : forall x in s, x <= a)
  proof: by
  rw [strictMonoOn_insert_iff]
  have : forall b in s, a < b -> f a < f b := by
    intro b hb hab
    cases (ha _ hb).not_gt hab
  tauto

中文:
引理 strictMonoOn_insert_iff_of_forall_le
  条件: {a : α} (ha : 对任意 x in s, x <= a)
  证明: by
  rw [strictMonoOn_insert_iff]
  have : forall b in s, a < b -> f a < f b := by
    intro b hb hab
    cases (ha _ hb).not_gt hab
  tauto

Depends on / 依赖: not_gt, strictMonoOn_insert_iff
-/
lemma strictMonoOn_insert_iff_of_forall_le {a : α} (ha : forall x in s, x <= a) :
    StrictMonoOn f (insert a s) ↔ (forall b in s, b < a -> f b < f a) ∧ StrictMonoOn f s := by
  rw [strictMonoOn_insert_iff]
  have : forall b in s, a < b -> f a < f b := by
    intro b hb hab
    cases (ha _ hb).not_gt hab
  tauto

/--
lemma `strictMonoOn_insert_iff_of_forall_ge` / 引理 `strictMonoOn_insert_iff_of_forall_ge`

English:
lemma strictMonoOn_insert_iff_of_forall_ge
  given: {a : α} (ha : forall x in s, a <= x)
  proof: by
  rw [strictMonoOn_insert_iff]
  have : forall b in s, b < a -> f b < f a := by
    intro b hb hab
    cases (ha _ hb).not_gt hab
  tauto

中文:
引理 strictMonoOn_insert_iff_of_forall_ge
  条件: {a : α} (ha : 对任意 x in s, a <= x)
  证明: by
  rw [strictMonoOn_insert_iff]
  have : forall b in s, b < a -> f b < f a := by
    intro b hb hab
    cases (ha _ hb).not_gt hab
  tauto

Depends on / 依赖: not_gt, strictMonoOn_insert_iff
-/
lemma strictMonoOn_insert_iff_of_forall_ge {a : α} (ha : forall x in s, a <= x) :
    StrictMonoOn f (insert a s) ↔ (forall b in s, a < b -> f a < f b) ∧ StrictMonoOn f s := by
  rw [strictMonoOn_insert_iff]
  have : forall b in s, b < a -> f b < f a := by
    intro b hb hab
    cases (ha _ hb).not_gt hab
  tauto

/--
lemma `strictAntiOn_insert_iff_of_forall_le` / 引理 `strictAntiOn_insert_iff_of_forall_le`

English:
lemma strictAntiOn_insert_iff_of_forall_le
  given: {a : α} (ha : forall x in s, x <= a)
  proof: by
  rw [strictAntiOn_insert_iff]
  have : forall b in s, a < b -> f b < f a := by
    intro b hb hab
    cases (ha _ hb).not_gt hab
  tauto

中文:
引理 strictAntiOn_insert_iff_of_forall_le
  条件: {a : α} (ha : 对任意 x in s, x <= a)
  证明: by
  rw [strictAntiOn_insert_iff]
  have : forall b in s, a < b -> f b < f a := by
    intro b hb hab
    cases (ha _ hb).not_gt hab
  tauto

Depends on / 依赖: not_gt, strictAntiOn_insert_iff
-/
lemma strictAntiOn_insert_iff_of_forall_le {a : α} (ha : forall x in s, x <= a) :
    StrictAntiOn f (insert a s) ↔ (forall b in s, b < a -> f a < f b) ∧ StrictAntiOn f s := by
  rw [strictAntiOn_insert_iff]
  have : forall b in s, a < b -> f b < f a := by
    intro b hb hab
    cases (ha _ hb).not_gt hab
  tauto

/--
lemma `strictAntiOn_insert_iff_of_forall_ge` / 引理 `strictAntiOn_insert_iff_of_forall_ge`

English:
lemma strictAntiOn_insert_iff_of_forall_ge
  given: {a : α} (ha : forall x in s, a <= x)
  proof: by
  rw [strictAntiOn_insert_iff]
  have : forall b in s, b < a -> f a < f b := by
    intro b hb hab
    cases (ha _ hb).not_gt hab
  tauto

中文:
引理 strictAntiOn_insert_iff_of_forall_ge
  条件: {a : α} (ha : 对任意 x in s, a <= x)
  证明: by
  rw [strictAntiOn_insert_iff]
  have : forall b in s, b < a -> f a < f b := by
    intro b hb hab
    cases (ha _ hb).not_gt hab
  tauto

Depends on / 依赖: not_gt, strictAntiOn_insert_iff
-/
lemma strictAntiOn_insert_iff_of_forall_ge {a : α} (ha : forall x in s, a <= x) :
    StrictAntiOn f (insert a s) ↔ (forall b in s, a < b -> f b < f a) ∧ StrictAntiOn f s := by
  rw [strictAntiOn_insert_iff]
  have : forall b in s, b < a -> f a < f b := by
    intro b hb hab
    cases (ha _ hb).not_gt hab
  tauto

end strictMono

namespace Function

open Set

/--
theorem `monotoneOn_of_rightInvOn_of_mapsTo` / 定理 `monotoneOn_of_rightInvOn_of_mapsTo`

English:
theorem monotoneOn_of_rightInvOn_of_mapsTo
  statement: {α β : Type*} [PartialOrder α] [LinearOrder β]
  proof: by
  rintro x xs y ys l
  rcases le_total (ψ x) (ψ y) with (ψxy | ψyx)
  · exact ψxy
  · have := hφ (ψts ys) (ψts xs) ψyx
    rw [φψs.eq ys]; rw [φψs.eq xs] at this
    induction le_antisymm l this
    exact le_refl _

中文:
定理 monotoneOn_of_rightInvOn_of_mapsTo
  结论: {α β : 类型} [PartialOrder α] [LinearOrder β]
  证明: by
  rintro x xs y ys l
  rcases le_total (ψ x) (ψ y) with (ψxy | ψyx)
  · exact ψxy
  · have := hφ (ψts ys) (ψts xs) ψyx
    rw [φψs.eq ys]; rw [φψs.eq xs] at this
    induction le_antisymm l this
    exact le_refl _

Depends on / 依赖: le_antisymm, le_refl, le_total, s.eq
-/
theorem monotoneOn_of_rightInvOn_of_mapsTo {α β : Type*} [PartialOrder α] [LinearOrder β]
    {φ : β -> α} {ψ : α -> β} {t : Set β} {s : Set α} (hφ : MonotoneOn φ t)
    (φψs : Set.RightInvOn ψ φ s) (ψts : Set.MapsTo ψ s t) : MonotoneOn ψ s := by
  rintro x xs y ys l
  rcases le_total (ψ x) (ψ y) with (ψxy | ψyx)
  · exact ψxy
  · have := hφ (ψts ys) (ψts xs) ψyx
    rw [φψs.eq ys]; rw [φψs.eq xs] at this
    induction le_antisymm l this
    exact le_refl _

/--
theorem `antitoneOn_of_rightInvOn_of_mapsTo` / 定理 `antitoneOn_of_rightInvOn_of_mapsTo`

English:
theorem antitoneOn_of_rightInvOn_of_mapsTo
  statement: [PartialOrder α] [LinearOrder β]
  proof: (monotoneOn_of_rightInvOn_of_mapsTo hφ.dual_left φψs ψts).dual_right

中文:
定理 antitoneOn_of_rightInvOn_of_mapsTo
  结论: [PartialOrder α] [LinearOrder β]
  证明: (monotoneOn_of_rightInvOn_of_mapsTo hφ.dual_left φψs ψts).dual_right

Depends on / 依赖: dual_left, dual_right, monotoneOn_of_rightInvOn_of_mapsTo
-/
theorem antitoneOn_of_rightInvOn_of_mapsTo [PartialOrder α] [LinearOrder β]
    {φ : β -> α} {ψ : α -> β} {t : Set β} {s : Set α} (hφ : AntitoneOn φ t)
    (φψs : Set.RightInvOn ψ φ s) (ψts : Set.MapsTo ψ s t) : AntitoneOn ψ s :=
  (monotoneOn_of_rightInvOn_of_mapsTo hφ.dual_left φψs ψts).dual_right

end Function
