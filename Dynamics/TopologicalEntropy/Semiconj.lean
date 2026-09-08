/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy

/-!
# Topological entropy of the image of a set under a semiconjugacy

Consider two dynamical systems `(X, S)` and `(Y, T)` together with a semiconjugacy `φ`:


```
X ---S--> X
|         |
φ         φ
|         |
v         v
Y ---T--> Y
```

We relate the topological entropy of a subset `F ⊆ X` with the topological entropy
of its image `φ '' F ⊆ Y`.

The best-known theorem is that, if all maps are uniformly continuous, then
`coverEntropy T (φ '' F) ≤ coverEntropy S F`. This is theorem
`coverEntropy_image_le_of_uniformContinuous` herein. We actually prove the much more general
statement that `coverEntropy T (φ '' F) = coverEntropy S F` if `X` is endowed with the pullback
by `φ` of the uniform structure of `Y`.

This more general statement has another direct consequence: if `F` is `S`-invariant, then the
topological entropy of the restriction of `S` to `F` is exactly `coverEntropy S F`. This
corollary is essential: in most references, the entropy of an invariant subset (or subsystem) `F` is
defined as the entropy of the restriction to `F` of the system. We chose instead to give a direct
definition of the topological entropy of a subset, so as to avoid working with subtypes. Theorem
`coverEntropy_restrict` shows that this choice is coherent with the literature.

## Implementation notes
We use only the definition of the topological entropy using covers; the simplest version of
`IsDynCoverOf.image` for nets fails.

## Main results
- `coverEntropy_image_of_comap`/`coverEntropyInf_image_of_comap`: the entropy of `φ '' F` equals
  the entropy of `F` if `X` is endowed with the pullback by `φ` of the uniform structure of `Y`.
- `coverEntropy_image_le_of_uniformContinuous`/`coverEntropyInf_image_le_of_uniformContinuous`:
  the entropy of `φ '' F` is lower than the entropy of `F` if `φ` is uniformly continuous.
- `coverEntropy_restrict`: the entropy of the restriction of `S` to an invariant set `F` is
  `coverEntropy S F`.

## Tags
entropy, semiconjugacy
-/

public section

open Function Prod Set Uniformity UniformSpace
open scoped SetRel

namespace Dynamics

variable {X Y : Type*} {s F : Set X} {V : SetRel Y Y} {S : X → X} {T : Y → Y} {φ : X → Y} {n : ℕ}

/-
**Dynamics.IsDynCoverOf.image** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics.IsDynCoverOf`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {s F : Set X} {V : SetRel Y Y} {S : X → X}
 {T : Y → Y} {φ : X → Y} {n : ℕ},   Function.Semiconj φ S T →     Dynamics.IsDyn
CoverOf S F (Prod.map φ φ ⁻¹' V) n s → Dynamics.IsDynCoverOf T (φ '' F) V n (φ '
' s)
参数：Prod.map φ φ ⁻¹' V；φ '' F；φ '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Semiconj.preimage_dynEntourage`：∀ {X : Type u_1} {Y : Type u_2}
 {S : X → X} {T : Y → Y} {φ : X → Y},   Function.Semiconj φ S T →     ∀ (U : Set
 (Y × Y)) (n : ℕ),       Prod…
-/
lemma IsDynCoverOf.image (h : Semiconj φ S T) (h' : IsDynCoverOf S F (map φ φ ⁻¹' V) n s) :
    IsDynCoverOf T (φ '' F) V n (φ '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := h' hx
  refine ⟨_, Set.mem_image_of_mem _ hy, show (x, y) ∈ map φ φ ⁻¹' dynEntourage T V n from ?_⟩
  rwa [h.preimage_dynEntourage V n]
/-
**Dynamics.IsDynCoverOf.preimage** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics.IsDynCoverO
f`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {F : Set X} {V : SetRel Y Y} {S : X → X} {
T : Y → Y} {φ : X → Y} {n : ℕ},   Function.Semiconj φ S T →     ∀ [V.IsSymm] {t 
: Finset Y},       Dynamics.IsDynCoverOf T (φ '' F) V n ↑t →         ∃ s, Dynami
cs.IsDynCoverOf S F (Prod.map φ φ ⁻¹' V.comp V) n ↑s ∧ s.card ≤ t.card
参数：φ '' F；Prod.map φ φ ⁻¹' V.comp V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Dynamics.isDynCoverOf_empty`：∀ {X : Type u_1} {T : X → X} {U : SetRel X 
X} {s : Set X} {n : ℕ}, Dynamics.IsDynCoverOf T ∅ U n s
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_empty`：card_empty : #(∅ : Finset α) = 0
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `Dynamics.IsDynCoverOf.nonempty_inter`：∀ {X : Type u_1} {T : X → X} {U : 
SetRel X X} {F : Set X} {n : ℕ} [U.IsSymm] {s : Finset X},   Dynamics.IsDynCover
Of T F U n ↑s →     ∃ t,  …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Function.Semiconj.preimage_dynEntourage`：∀ {X : Type u_1} {Y : Type u_2}
 {S : X → X} {T : Y → Y} {φ : X → Y},   Function.Semiconj φ S T →     ∀ (U : Set
 (Y × Y)) (n : ℕ),       Prod…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用引理 `Dynamics.dynEntourage_comp_subset`：dynEntourage_comp_subset (T : X -> X)
 (U V : SetRel X X) (n : Nat) : (dynEntourage T U n) ○ (dynEntourage T V n) subs
eteq dynEntourage T (U …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.nonempty_def`：nonempty_def : s.Nonempty ↔ exists x, x in s
-/
lemma IsDynCoverOf.preimage (h : Semiconj φ S T) [V.IsSymm] {t : Finset Y}
    (h' : IsDynCoverOf T (φ '' F) V n t) :
    ∃ s : Finset X, IsDynCoverOf S F ((map φ φ) ⁻¹' (V ○ V)) n s ∧ s.card ≤ t.card := by
  classical
  rcases isEmpty_or_nonempty X with _ | _
  · exact ⟨∅, eq_empty_of_isEmpty F ▸ ⟨isDynCoverOf_empty, Finset.card_empty ▸ zero_le⟩⟩
  -- If `t` is a dynamical cover of `φ '' F`, then we want to choose one preimage by `φ` for each
  -- element of `t`. This is complicated by the fact that `t` may not be a subset of `φ '' F`,
  -- and may not even be in the range of `φ`. Hence, we first modify `t` to make it a subset
  -- of `φ '' F`. This requires taking larger entourages.
  obtain ⟨s, s_cover, s_card, s_inter⟩ := h'.nonempty_inter
  choose! g g_rel g_mem using fun (x : Y) (h : x ∈ s) ↦ nonempty_def.1 (s_inter x h)
  choose! f _ φ_f using fun (y : Y) (hy : y ∈ φ '' F) ↦ hy
  refine ⟨s.image (f ∘ g), fun x hx ↦ ?_, Finset.card_image_le.trans s_card⟩
  simp only [Finset.coe_image, comp_apply, mem_image, SetLike.mem_coe, ← h.preimage_dynEntourage,
    mem_preimage, map_apply, exists_exists_and_eq_and]
  obtain ⟨y, hy, hxy⟩ := s_cover (Set.mem_image_of_mem _ hx)
  refine ⟨y, hy, dynEntourage_comp_subset _ _ _ _ ⟨_, hxy, ?_⟩⟩
  rw [φ_f _ (g_mem _ hy)]
  exact g_rel _ hy
/-
**Dynamics.le_coverMincard_image** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：le_coverMincard_image (h : Semiconj φ S T) (F : Set X) [V.IsSymm] (n : Nat
) : coverMincard S F ((map φ φ) ⁻¹' (V ○ V)) n <= coverMincard T (φ '' F) V n
参数：h : Semiconj φ S T；F : Set X；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Dynamics.coverMincard_finite_iff`：coverMincard_finite_iff (T : X -> X) (
F : Set X) (U : SetRel X X) (n : Nat) : coverMincard T F U n < ⊤ ↔ exists s : Fi
nset X, IsDynCoverOf T…
· 使用定理 `Dynamics.IsDynCoverOf.preimage`：∀ {X : Type u_1} {Y : Type u_2} {F : Set
 X} {V : SetRel Y Y} {S : X → X} {T : Y → Y} {φ : X → Y} {n : ℕ},   Function.Sem
iconj φ S T →     ∀ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Dynamics.IsDynCoverOf.coverMincard_le_card`：∀ {X : Type u_1} {T : X → X}
 {U : SetRel X X} {F : Set X} {n : ℕ} {s : Finset X},   Dynamics.IsDynCoverOf T 
F U n ↑s → Dynamics.coverMincard…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
-/
lemma le_coverMincard_image (h : Semiconj φ S T) (F : Set X) [V.IsSymm] (n : ℕ) :
    coverMincard S F ((map φ φ) ⁻¹' (V ○ V)) n ≤ coverMincard T (φ '' F) V n := by
  rcases eq_top_or_lt_top (coverMincard T (φ '' F) V n) with h' | h'
  · exact h' ▸ le_top
  obtain ⟨t, t_cover, t_card⟩ := (coverMincard_finite_iff T (φ '' F) V n).1 h'
  obtain ⟨s, s_cover, s_card⟩ := t_cover.preimage h
  rw [← t_card]
  exact s_cover.coverMincard_le_card.trans (WithTop.coe_le_coe.2 s_card)
/-
**Dynamics.coverMincard_image_le** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverMincard_image_le (h : Semiconj φ S T) (F : Set X) (V : SetRel Y Y) (n
 : Nat) : coverMincard T (φ '' F) V n <= coverMincard S F ((map φ φ) ⁻¹' V) n
参数：h : Semiconj φ S T；F : Set X；V : SetRel Y Y；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Dynamics.coverMincard_finite_iff`：coverMincard_finite_iff (T : X -> X) (
F : Set X) (U : SetRel X X) (n : Nat) : coverMincard T F U n < ⊤ ↔ exists s : Fi
nset X, IsDynCoverOf T…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dynamics.IsDynCoverOf.image`：∀ {X : Type u_1} {Y : Type u_2} {s F : Set 
X} {V : SetRel Y Y} {S : X → X} {T : Y → Y} {φ : X → Y} {n : ℕ},   Function.Semi
conj φ S T →     …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Dynamics.IsDynCoverOf.coverMincard_le_card`：∀ {X : Type u_1} {T : X → X}
 {U : SetRel X X} {F : Set X} {n : ℕ} {s : Finset X},   Dynamics.IsDynCoverOf T 
F U n ↑s → Dynamics.coverMincard…
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s
-/
lemma coverMincard_image_le (h : Semiconj φ S T) (F : Set X) (V : SetRel Y Y) (n : ℕ) :
    coverMincard T (φ '' F) V n ≤ coverMincard S F ((map φ φ) ⁻¹' V) n := by
  classical
  rcases eq_top_or_lt_top (coverMincard S F ((map φ φ) ⁻¹' V) n) with h' | h'
  · exact h' ▸ le_top
  obtain ⟨s, s_cover, s_card⟩ := (coverMincard_finite_iff S F ((map φ φ) ⁻¹' V) n).1 h'
  rw [← s_card]
  have := s_cover.image h
  rw [← s.coe_image] at this
  exact this.coverMincard_le_card.trans (WithTop.coe_le_coe.2 s.card_image_le)

open ENNReal EReal ExpGrowth Filter
/-
**Dynamics.le_coverEntropyEntourage_image** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：le_coverEntropyEntourage_image (h : Semiconj φ S T) (F : Set X) [V.IsSymm]
 : coverEntropyEntourage S F ((map φ φ) ⁻¹' (V ○ V)) <= coverEntropyEntourage T 
(φ '' F) V
参数：h : Semiconj φ S T；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthSup_monotone`：expGrowthSup_monotone : Monotone expGro
wthSup
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.le_coverMincard_image`：le_coverMincard_image (h : Semiconj φ S 
T) (F : Set X) [V.IsSymm] (n : Nat) : coverMincard S F ((map φ φ) ⁻¹' (V ○ V)) n
 <= coverMincard T (…
-/
lemma le_coverEntropyEntourage_image (h : Semiconj φ S T) (F : Set X) [V.IsSymm] :
    coverEntropyEntourage S F ((map φ φ) ⁻¹' (V ○ V)) ≤ coverEntropyEntourage T (φ '' F) V :=
  expGrowthSup_monotone fun n ↦ ENat.toENNReal_mono (le_coverMincard_image h F n)
/-
**Dynamics.le_coverEntropyInfEntourage_image** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics
`。
形式化陈述：le_coverEntropyInfEntourage_image (h : Semiconj φ S T) (F : Set X) [V.IsSy
mm] : coverEntropyInfEntourage S F ((map φ φ) ⁻¹' (V ○ V)) <= coverEntropyInfEnt
ourage T (φ '' F) V
参数：h : Semiconj φ S T；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthInf_monotone`：expGrowthInf_monotone : Monotone expGro
wthInf
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.le_coverMincard_image`：le_coverMincard_image (h : Semiconj φ S 
T) (F : Set X) [V.IsSymm] (n : Nat) : coverMincard S F ((map φ φ) ⁻¹' (V ○ V)) n
 <= coverMincard T (…
-/
lemma le_coverEntropyInfEntourage_image (h : Semiconj φ S T) (F : Set X) [V.IsSymm] :
    coverEntropyInfEntourage S F ((map φ φ) ⁻¹' (V ○ V)) ≤ coverEntropyInfEntourage T (φ '' F) V :=
  expGrowthInf_monotone fun n ↦ ENat.toENNReal_mono (le_coverMincard_image h F n)
/-
**Dynamics.coverEntropyEntourage_image_le** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyEntourage_image_le (h : Semiconj φ S T) (F : Set X) (V : SetRe
l Y Y) : coverEntropyEntourage T (φ '' F) V <= coverEntropyEntourage S F ((map φ
 φ) ⁻¹' V)
参数：h : Semiconj φ S T；F : Set X；V : SetRel Y Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthSup_monotone`：expGrowthSup_monotone : Monotone expGro
wthSup
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.coverMincard_image_le`：coverMincard_image_le (h : Semiconj φ S 
T) (F : Set X) (V : SetRel Y Y) (n : Nat) : coverMincard T (φ '' F) V n <= cover
Mincard S F ((map φ …
-/
lemma coverEntropyEntourage_image_le (h : Semiconj φ S T) (F : Set X) (V : SetRel Y Y) :
    coverEntropyEntourage T (φ '' F) V ≤ coverEntropyEntourage S F ((map φ φ) ⁻¹' V) :=
  expGrowthSup_monotone fun n ↦ ENat.toENNReal_mono (coverMincard_image_le h F V n)
/-
**Dynamics.coverEntropyInfEntourage_image_le** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics
`。
形式化陈述：coverEntropyInfEntourage_image_le (h : Semiconj φ S T) (F : Set X) (V : Se
tRel Y Y) : coverEntropyInfEntourage T (φ '' F) V <= coverEntropyInfEntourage S 
F ((map φ φ) ⁻¹' V)
参数：h : Semiconj φ S T；F : Set X；V : SetRel Y Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthInf_monotone`：expGrowthInf_monotone : Monotone expGro
wthInf
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.coverMincard_image_le`：coverMincard_image_le (h : Semiconj φ S 
T) (F : Set X) (V : SetRel Y Y) (n : Nat) : coverMincard T (φ '' F) V n <= cover
Mincard S F ((map φ …
-/
lemma coverEntropyInfEntourage_image_le (h : Semiconj φ S T) (F : Set X) (V : SetRel Y Y) :
    coverEntropyInfEntourage T (φ '' F) V ≤ coverEntropyInfEntourage S F ((map φ φ) ⁻¹' V) :=
  expGrowthInf_monotone fun n ↦ ENat.toENNReal_mono (coverMincard_image_le h F V n)

/-- The entropy of `φ '' F` equals the entropy of `F` if `X` is endowed with the pullback by `φ`
  of the uniform structure of `Y`. -/
/-
**Dynamics.coverEntropy_image_of_comap** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropy_image_of_comap (u : UniformSpace Y) {S : X -> X} {T : Y -> Y}
 {φ : X -> Y} (h : Semiconj φ S T) (F : Set X) : coverEntropy T (φ '' F) = @cove
rEntropy X (comap φ u) S F
参数：u : UniformSpace Y；h : Semiconj φ S T；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Dynamics.coverEntropyEntourage_antitone`：coverEntropyEntourage_antitone 
(T : X -> X) (F : Set X) : Antitone fun U : SetRel X X => coverEntropyEntourage 
T F U
· 使用引理 `SetRel.symmetrize_subset_self`：symmetrize_subset_self : R.symmetrize sub
seteq R
· 使用引理 `Dynamics.coverEntropyEntourage_image_le`：coverEntropyEntourage_image_le 
(h : Semiconj φ S T) (F : Set X) (V : SetRel Y Y) : coverEntropyEntourage T (φ '
' F) V <= coverEntropyEntoura…
· 使用引理 `Dynamics.coverEntropyEntourage_le_coverEntropy`：coverEntropyEntourage_le
_coverEntropy (T : X -> X) (F : Set X) (h : U in 𝓤 X) : coverEntropyEntourage T 
F U <= coverEntropy T F
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_comap`：uniformity_comap {_ : UniformSpace β} (f : α -> β) : 𝓤
[UniformSpace.comap f ‹_›] = comap (Prod.map f f) (𝓤 β)
· 使用定理 `Filter.mem_comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} {m : α 
→ β} {s : Set α}, s ∈ Filter.comap m g ↔ ∃ t ∈ g, m ⁻¹' t ⊆ s
· 使用定理 `symmetrize_mem_uniformity`：symmetrize_mem_uniformity {V : SetRel α α} (h
 : V in 𝓤 α) : SetRel.symmetrize V in 𝓤 α
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `comp_symm_mem_uniformity_sets`：comp_symm_mem_uniformity_sets {s : SetRel
 α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用引理 `Dynamics.le_coverEntropyEntourage_image`：le_coverEntropyEntourage_image 
(h : Semiconj φ S T) (F : Set X) [V.IsSymm] : coverEntropyEntourage S F ((map φ 
φ) ⁻¹' (V ○ V)) <= coverEntro…

--- 原说明 ---
The entropy of `φ '' F` equals the entropy of `F` if `X` is endowed with the pul
lback by `φ`
  of the uniform structure of `Y`.
-/
theorem coverEntropy_image_of_comap (u : UniformSpace Y) {S : X → X} {T : Y → Y} {φ : X → Y}
    (h : Semiconj φ S T) (F : Set X) :
    coverEntropy T (φ '' F) = @coverEntropy X (comap φ u) S F := by
  let : UniformSpace X := comap φ u
  apply le_antisymm
  · refine iSup₂_le fun V V_uni ↦
      (coverEntropyEntourage_antitone _ _ SetRel.symmetrize_subset_self).trans <|
      (coverEntropyEntourage_image_le h F _).trans ?_
    apply coverEntropyEntourage_le_coverEntropy
    rw [uniformity_comap φ, mem_comap]
    exact ⟨_, symmetrize_mem_uniformity V_uni, .rfl⟩
  · refine iSup₂_le fun U U_uni ↦ ?_
    simp only [uniformity_comap φ, mem_comap] at U_uni
    obtain ⟨V, V_uni, V_sub⟩ := U_uni
    obtain ⟨W, W_uni, W_symm, W_V⟩ := comp_symm_mem_uniformity_sets V_uni
    apply (coverEntropyEntourage_antitone S F ((preimage_mono W_V).trans V_sub)).trans
    apply (le_coverEntropyEntourage_image h F).trans
    exact coverEntropyEntourage_le_coverEntropy T (φ '' F) W_uni

/-- The entropy of `φ '' F` equals the entropy of `F` if `X` is endowed with the pullback by `φ`
  of the uniform structure of `Y`. This version uses a `liminf`. -/
/-
**Dynamics.coverEntropyInf_image_of_comap** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInf_image_of_comap (u : UniformSpace Y) {S : X -> X} {T : Y ->
 Y} {φ : X -> Y} (h : Semiconj φ S T) (F : Set X) : coverEntropyInf T (φ '' F) =
 @coverEntropyInf X (comap φ u) S F
参数：u : UniformSpace Y；h : Semiconj φ S T；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Dynamics.coverEntropyInfEntourage_antitone`：coverEntropyInfEntourage_ant
itone (T : X -> X) (F : Set X) : Antitone fun U : SetRel X X => coverEntropyInfE
ntourage T F U
· 使用引理 `SetRel.symmetrize_subset_self`：symmetrize_subset_self : R.symmetrize sub
seteq R
· 使用引理 `Dynamics.coverEntropyInfEntourage_image_le`：coverEntropyInfEntourage_ima
ge_le (h : Semiconj φ S T) (F : Set X) (V : SetRel Y Y) : coverEntropyInfEntoura
ge T (φ '' F) V <= coverEntropyI…
· 使用引理 `Dynamics.coverEntropyInfEntourage_le_coverEntropyInf`：coverEntropyInfEnt
ourage_le_coverEntropyInf (T : X -> X) (F : Set X) (h : U in 𝓤 X) : coverEntropy
InfEntourage T F U <= coverEntropyInf T F
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_comap`：uniformity_comap {_ : UniformSpace β} (f : α -> β) : 𝓤
[UniformSpace.comap f ‹_›] = comap (Prod.map f f) (𝓤 β)
· 使用定理 `Filter.mem_comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} {m : α 
→ β} {s : Set α}, s ∈ Filter.comap m g ↔ ∃ t ∈ g, m ⁻¹' t ⊆ s
· 使用定理 `symmetrize_mem_uniformity`：symmetrize_mem_uniformity {V : SetRel α α} (h
 : V in 𝓤 α) : SetRel.symmetrize V in 𝓤 α
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `comp_symm_mem_uniformity_sets`：comp_symm_mem_uniformity_sets {s : SetRel
 α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用引理 `Dynamics.le_coverEntropyInfEntourage_image`：le_coverEntropyInfEntourage_
image (h : Semiconj φ S T) (F : Set X) [V.IsSymm] : coverEntropyInfEntourage S F
 ((map φ φ) ⁻¹' (V ○ V)) <= cove…

--- 原说明 ---
The entropy of `φ '' F` equals the entropy of `F` if `X` is endowed with the pul
lback by `φ`
  of the uniform structure of `Y`. This version uses a `liminf`.
-/
theorem coverEntropyInf_image_of_comap (u : UniformSpace Y) {S : X → X} {T : Y → Y} {φ : X → Y}
    (h : Semiconj φ S T) (F : Set X) :
    coverEntropyInf T (φ '' F) = @coverEntropyInf X (comap φ u) S F := by
  let : UniformSpace X := comap φ u
  apply le_antisymm
  · refine iSup₂_le fun V V_uni ↦
      (coverEntropyInfEntourage_antitone _ _ SetRel.symmetrize_subset_self).trans <|
      (coverEntropyInfEntourage_image_le h F _).trans ?_
    apply coverEntropyInfEntourage_le_coverEntropyInf
    rw [uniformity_comap φ, mem_comap]
    exact ⟨_, symmetrize_mem_uniformity V_uni, .rfl⟩
  · refine iSup₂_le fun U U_uni ↦ ?_
    simp only [uniformity_comap φ, mem_comap] at U_uni
    obtain ⟨V, V_uni, V_sub⟩ := U_uni
    obtain ⟨W, W_uni, W_symm, W_V⟩ := comp_symm_mem_uniformity_sets V_uni
    apply (coverEntropyInfEntourage_antitone S F ((preimage_mono W_V).trans V_sub)).trans
    apply (le_coverEntropyInfEntourage_image h F).trans
    exact coverEntropyInfEntourage_le_coverEntropyInf T (φ '' F) W_uni

open Subtype
/-
**Dynamics.coverEntropy_restrict_subset** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropy_restrict_subset [UniformSpace X] {T : X -> X} {F G : Set X} (
hF : F subseteq G) (hG : MapsTo T G G) : coverEntropy (hG.restrict T G G) (val ⁻
¹' F) = coverEntropy T F
参数：hF : F subseteq G；hG : MapsTo T G G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Dynamics.coverEntropy_image_of_comap`：coverEntropy_image_of_comap (u : U
niformSpace Y) {S : X -> X} {T : Y -> Y} {φ : X -> Y} (h : Semiconj φ S T) (F : 
Set X) : coverEntropy T (φ…
· 使用定理 `Set.MapsTo.val_restrict_apply`：∀ {α : Type u_1} {β : Type u_2} {s : Set 
α} {t : Set β} {f : α → β} (h : Set.MapsTo f s t) (x : ↑s),   ↑(Set.MapsTo.restr
ict f s t h x) = f …
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
-/
lemma coverEntropy_restrict_subset [UniformSpace X] {T : X → X} {F G : Set X} (hF : F ⊆ G)
    (hG : MapsTo T G G) :
    coverEntropy (hG.restrict T G G) (val ⁻¹' F) = coverEntropy T F := by
  rw [← coverEntropy_image_of_comap _ hG.val_restrict_apply (val ⁻¹' F), image_preimage_coe G F,
    inter_eq_right.2 hF]
/-
**Dynamics.coverEntropyInf_restrict_subset** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInf_restrict_subset [UniformSpace X] {T : X -> X} {F G : Set X
} (hF : F subseteq G) (hG : MapsTo T G G) : coverEntropyInf (hG.restrict T G G) 
(val ⁻¹' F) = coverEntropyInf T F
参数：hF : F subseteq G；hG : MapsTo T G G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Dynamics.coverEntropyInf_image_of_comap`：coverEntropyInf_image_of_comap 
(u : UniformSpace Y) {S : X -> X} {T : Y -> Y} {φ : X -> Y} (h : Semiconj φ S T)
 (F : Set X) : coverEntropyIn…
· 使用定理 `Set.MapsTo.val_restrict_apply`：∀ {α : Type u_1} {β : Type u_2} {s : Set 
α} {t : Set β} {f : α → β} (h : Set.MapsTo f s t) (x : ↑s),   ↑(Set.MapsTo.restr
ict f s t h x) = f …
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
-/
lemma coverEntropyInf_restrict_subset [UniformSpace X] {T : X → X} {F G : Set X} (hF : F ⊆ G)
    (hG : MapsTo T G G) :
    coverEntropyInf (hG.restrict T G G) (val ⁻¹' F) = coverEntropyInf T F := by
  rw [← coverEntropyInf_image_of_comap _ hG.val_restrict_apply (val ⁻¹' F), image_preimage_coe G F,
    inter_eq_right.2 hF]

/-- The entropy of the restriction of `T` to an invariant set `F` is `coverEntropy T F`. This
/-
**Dynamics.justifies** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem justifies our definition of `coverEntropy T F`. -/
/-
**Dynamics.coverEntropy_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropy_restrict [UniformSpace X] {T : X -> X} {F : Set X} (h : MapsT
o T F F) : coverEntropy (h.restrict T F F) univ = coverEntropy T F
参数：h : MapsTo T F F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Dynamics.coverEntropy_restrict_subset`：coverEntropy_restrict_subset [Uni
formSpace X] {T : X -> X} {F G : Set X} (hF : F subseteq G) (hG : MapsTo T G G) 
: coverEntropy (hG.restrict…
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ

--- 原说明 ---
The entropy of the restriction of `T` to an invariant set `F` is `coverEntropy T
 F`. This
theorem justifies our definition of `coverEntropy T F`.
-/
theorem coverEntropy_restrict [UniformSpace X] {T : X → X} {F : Set X} (h : MapsTo T F F) :
    coverEntropy (h.restrict T F F) univ = coverEntropy T F := by
  rw [← coverEntropy_restrict_subset Subset.rfl h, coe_preimage_self F]

/-- The entropy of `φ '' F` is at most the entropy of `F` if `φ` is uniformly continuous. -/
/-
**Dynamics.coverEntropy_image_le_of_uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 
`Dynamics`。
形式化陈述：coverEntropy_image_le_of_uniformContinuous [UniformSpace X] [UniformSpace 
Y] {S : X -> X} {T : Y -> Y} {φ : X -> Y} (h : Semiconj φ S T) (h' : UniformCont
inuous φ) (F : Set X) : coverEntropy T (φ '' F) <= coverEntropy S F
参数：h : Semiconj φ S T；h' : UniformContinuous φ；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dynamics.coverEntropy_image_of_comap`：coverEntropy_image_of_comap (u : U
niformSpace Y) {S : X -> X} {T : Y -> Y} {φ : X -> Y} (h : Semiconj φ S T) (F : 
Set X) : coverEntropy T (φ…
· 使用引理 `Dynamics.coverEntropy_antitone`：coverEntropy_antitone (T : X -> X) (F : 
Set X) : Antitone fun (u : UniformSpace X) => @coverEntropy X u T F
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `uniformContinuous_iff_le_comap`：uniformContinuous_iff_le_comap {α β} {uα
 : UniformSpace α} {uβ : UniformSpace β} {f : α -> β} : UniformContinuous f ↔ uα
 <= uβ.comap f

--- 原说明 ---
The entropy of `φ '' F` is at most the entropy of `F` if `φ` is uniformly contin
uous.
-/
theorem coverEntropy_image_le_of_uniformContinuous [UniformSpace X] [UniformSpace Y] {S : X → X}
    {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T) (h' : UniformContinuous φ) (F : Set X) :
    coverEntropy T (φ '' F) ≤ coverEntropy S F := by
  rw [coverEntropy_image_of_comap _ h F]
  exact coverEntropy_antitone S F (uniformContinuous_iff_le_comap.1 h')

/-- The entropy of `φ '' F` is at most the entropy of `F` if `φ` is uniformly continuous. This
  version uses a `liminf`. -/
/-
**Dynamics.coverEntropyInf_image_le_of_uniformContinuous** 是 Mathlib 中的一个定理，位于命名
空间 `Dynamics`。
形式化陈述：coverEntropyInf_image_le_of_uniformContinuous [UniformSpace X] [UniformSpa
ce Y] {S : X -> X} {T : Y -> Y} {φ : X -> Y} (h : Semiconj φ S T) (h' : UniformC
ontinuous φ) (F : Set X) : coverEntropyInf T (φ '' F) <= coverEntropyInf S F
参数：h : Semiconj φ S T；h' : UniformContinuous φ；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dynamics.coverEntropyInf_image_of_comap`：coverEntropyInf_image_of_comap 
(u : UniformSpace Y) {S : X -> X} {T : Y -> Y} {φ : X -> Y} (h : Semiconj φ S T)
 (F : Set X) : coverEntropyIn…
· 使用引理 `Dynamics.coverEntropyInf_antitone`：coverEntropyInf_antitone (T : X -> X)
 (F : Set X) : Antitone fun (u : UniformSpace X) => @coverEntropyInf X u T F
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `uniformContinuous_iff_le_comap`：uniformContinuous_iff_le_comap {α β} {uα
 : UniformSpace α} {uβ : UniformSpace β} {f : α -> β} : UniformContinuous f ↔ uα
 <= uβ.comap f

--- 原说明 ---
The entropy of `φ '' F` is at most the entropy of `F` if `φ` is uniformly contin
uous. This
  version uses a `liminf`.
-/
theorem coverEntropyInf_image_le_of_uniformContinuous [UniformSpace X] [UniformSpace Y] {S : X → X}
    {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T) (h' : UniformContinuous φ) (F : Set X) :
    coverEntropyInf T (φ '' F) ≤ coverEntropyInf S F := by
  rw [coverEntropyInf_image_of_comap _ h F]
  exact coverEntropyInf_antitone S F (uniformContinuous_iff_le_comap.1 h')
/-
**Dynamics.coverEntropy_image_le_of_uniformContinuousOn_invariant** 是 Mathlib 中的
一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropy_image_le_of_uniformContinuousOn_invariant [UniformSpace X] [U
niformSpace Y] {S : X -> X} {T : Y -> Y} {φ : X -> Y} (h : Semiconj φ S T) {F G 
: Set X} (h' : UniformContinuousOn φ G) (hF : F subseteq G) (hG : MapsTo S G G) 
: coverEntropy T (φ '' F) <= coverEntropy S F
参数：h : Semiconj φ S T；h' : UniformContinuousOn φ G；hF : F subseteq G；hG : MapsTo
 S G G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Dynamics.coverEntropy_restrict_subset`：coverEntropy_restrict_subset [Uni
formSpace X] {T : X -> X} {F G : Set X} (hF : F subseteq G) (hG : MapsTo T G G) 
: coverEntropy (hG.restrict…
· 使用定理 `Set.domRestrict_apply`：domRestrict_apply (f : (a : α) -> π a) (s : Set α
) (x : s) : s.domRestrict f x = f x
· 使用定理 `Set.MapsTo.val_restrict_apply`：∀ {α : Type u_1} {β : Type u_2} {s : Set 
α} {t : Set β} {f : α → β} (h : Set.MapsTo f s t) (x : ↑s),   ↑(Set.MapsTo.restr
ict f s t h x) = f …
· 使用定理 `Function.Semiconj.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : 
α → α} {gb : β → β},   Function.Semiconj f ga gb → ∀ (x : α), f (ga x) = gb (f x
)
· 使用定理 `LE.le.trans_eq'`：∀ {α : Type u_1} {a b c : α} [inst : LE α], b ≤ a → b =
 c → c ≤ a
· 使用定理 `Dynamics.coverEntropy_image_le_of_uniformContinuous`：coverEntropy_image_
le_of_uniformContinuous [UniformSpace X] [UniformSpace Y] {S : X -> X} {T : Y ->
 Y} {φ : X -> Y} (h : Semiconj φ S T) (h'…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `uniformContinuousOn_iff_restrict`：uniformContinuousOn_iff_restrict [Unif
ormSpace α] [UniformSpace β] {f : α -> β} {s : Set α} : UniformContinuousOn f s 
↔ UniformContinuous (s…
· 使用定理 `Set.image_image_val_eq_domRestrict_image`：image_image_val_eq_domRestrict
_image {δ : Type*} {f : α -> δ} : f '' γ = β.domRestrict f '' γ
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
-/
lemma coverEntropy_image_le_of_uniformContinuousOn_invariant [UniformSpace X] [UniformSpace Y]
    {S : X → X} {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T) {F G : Set X}
    (h' : UniformContinuousOn φ G) (hF : F ⊆ G) (hG : MapsTo S G G) :
    coverEntropy T (φ '' F) ≤ coverEntropy S F := by
  rw [← coverEntropy_restrict_subset hF hG]
  have hφ : Semiconj (G.domRestrict φ) (hG.restrict S G G) T := by
    intro x
    rw [G.domRestrict_apply, G.domRestrict_apply, hG.val_restrict_apply, h.eq x]
  apply (coverEntropy_image_le_of_uniformContinuous hφ
    (uniformContinuousOn_iff_restrict.1 h') (val ⁻¹' F)).trans_eq'
  rw [← image_image_val_eq_domRestrict_image, image_preimage_coe G F, inter_eq_right.2 hF]
/-
**Dynamics.coverEntropyInf_image_le_of_uniformContinuousOn_invariant** 是 Mathlib
 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInf_image_le_of_uniformContinuousOn_invariant [UniformSpace X]
 [UniformSpace Y] {S : X -> X} {T : Y -> Y} {φ : X -> Y} (h : Semiconj φ S T) {F
 G : Set X} (h' : UniformContinuousOn φ G) (hF : F subseteq G) (hG : MapsTo S G 
G) : coverEntropyInf T (φ '' F) <= coverEntropyInf S F
参数：h : Semiconj φ S T；h' : UniformContinuousOn φ G；hF : F subseteq G；hG : MapsTo
 S G G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Dynamics.coverEntropyInf_restrict_subset`：coverEntropyInf_restrict_subse
t [UniformSpace X] {T : X -> X} {F G : Set X} (hF : F subseteq G) (hG : MapsTo T
 G G) : coverEntropyInf (hG.re…
· 使用定理 `Set.domRestrict_apply`：domRestrict_apply (f : (a : α) -> π a) (s : Set α
) (x : s) : s.domRestrict f x = f x
· 使用定理 `Set.MapsTo.val_restrict_apply`：∀ {α : Type u_1} {β : Type u_2} {s : Set 
α} {t : Set β} {f : α → β} (h : Set.MapsTo f s t) (x : ↑s),   ↑(Set.MapsTo.restr
ict f s t h x) = f …
· 使用定理 `Function.Semiconj.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : 
α → α} {gb : β → β},   Function.Semiconj f ga gb → ∀ (x : α), f (ga x) = gb (f x
)
· 使用定理 `LE.le.trans_eq'`：∀ {α : Type u_1} {a b c : α} [inst : LE α], b ≤ a → b =
 c → c ≤ a
· 使用定理 `Dynamics.coverEntropyInf_image_le_of_uniformContinuous`：coverEntropyInf_
image_le_of_uniformContinuous [UniformSpace X] [UniformSpace Y] {S : X -> X} {T 
: Y -> Y} {φ : X -> Y} (h : Semiconj φ S T) …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `uniformContinuousOn_iff_restrict`：uniformContinuousOn_iff_restrict [Unif
ormSpace α] [UniformSpace β] {f : α -> β} {s : Set α} : UniformContinuousOn f s 
↔ UniformContinuous (s…
· 使用定理 `Set.image_image_val_eq_domRestrict_image`：image_image_val_eq_domRestrict
_image {δ : Type*} {f : α -> δ} : f '' γ = β.domRestrict f '' γ
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
-/
lemma coverEntropyInf_image_le_of_uniformContinuousOn_invariant [UniformSpace X] [UniformSpace Y]
    {S : X → X} {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T) {F G : Set X}
    (h' : UniformContinuousOn φ G) (hF : F ⊆ G) (hG : MapsTo S G G) :
    coverEntropyInf T (φ '' F) ≤ coverEntropyInf S F := by
  rw [← coverEntropyInf_restrict_subset hF hG]
  have hφ : Semiconj (G.domRestrict φ) (hG.restrict S G G) T := by
    intro a
    rw [G.domRestrict_apply, G.domRestrict_apply, hG.val_restrict_apply, h.eq a]
  apply (coverEntropyInf_image_le_of_uniformContinuous hφ
    (uniformContinuousOn_iff_restrict.1 h') (val ⁻¹' F)).trans_eq'
  rw [← image_image_val_eq_domRestrict_image, image_preimage_coe G F, inter_eq_right.2 hF]

end Dynamics

