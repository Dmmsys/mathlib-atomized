/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Data.Finite.Sigma
public import Mathlib.Topology.Spectral.Prespectral

/-!
# Compact open covered sets

In this file we define the notion of a compact-open covered set with respect to a family of
maps `fᵢ : X i → S`. A set `U` is compact-open covered by the family `fᵢ` if it is the finite
union of images of compact open sets in the `X i`.

This notion is not interesting, if the `fᵢ` are open maps (see `IsCompactOpenCovered.of_isOpenMap`).

This is used to define the fpqc topology of schemes, there a cover is given by a family of flat
morphisms such that every compact open is compact-open covered.

## Main results

- `IsCompactOpenCovered.of_isOpenMap`: If all the `fᵢ` are open maps, then every compact open
  of `S` is compact-open covered.
-/

@[expose] public section

open TopologicalSpace Opens

/-- A set `U` is compact-open covered by the family `fᵢ : X i → S`, if
`U` is the finite union of images of compact open sets in the `X i`. -/
/-
**IsCompactOpenCovered** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCompactOpenCovered {S ι : Type*} {X : ι -> Type*} (f : forall i, X i -> 
S) [forall i, TopologicalSpace (X i)] (U : Set S) : Prop
参数：f : forall i, X i -> S；X i；U : Set S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `U` is compact-open covered by the family `fᵢ : X i → S`, if
`U` is the finite union of images of compact open sets in the `X i`.
-/
def IsCompactOpenCovered {S ι : Type*} {X : ι → Type*} (f : ∀ i, X i → S)
    [∀ i, TopologicalSpace (X i)] (U : Set S) : Prop :=
  ∃ (s : Set ι) (_ : s.Finite) (V : ∀ i ∈ s, Opens (X i)),
    (∀ (i : ι) (h : i ∈ s), IsCompact (V i h).1) ∧
    ⋃ (i : ι) (h : i ∈ s), (f i) '' (V i h) = U

namespace IsCompactOpenCovered

variable {S ι : Type*} {X : ι → Type*} {f : ∀ i, X i → S} [∀ i, TopologicalSpace (X i)] {U : Set S}

/-
**IsCompactOpenCovered.empty** 是 Mathlib 中的一个引理，位于命名空间 `IsCompactOpenCovered`。
形式化陈述：empty : IsCompactOpenCovered f ∅
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `isCompact_empty`：isCompact_empty : IsCompact (∅ : Set X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma empty : IsCompactOpenCovered f ∅ :=
  ⟨∅, Set.finite_empty, fun _ _ ↦ ⟨∅, isOpen_empty⟩, fun _ _ ↦ isCompact_empty, by simp⟩
/-
**IsCompactOpenCovered.iff_of_unique** 是 Mathlib 中的一个引理，位于命名空间 `IsCompactOpenCov
ered`。
形式化陈述：iff_of_unique [Unique ι] : IsCompactOpenCovered f U ↔ exists (V : Opens (X
 default)), IsCompact V.1 ∧ f default '' V.1 = U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_singleton_of_unique`：eq_empty_or_singleton_of_unique [Un
ique α] (s : Set α) : s = ∅ ∨ s = {default}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma iff_of_unique [Unique ι] :
    IsCompactOpenCovered f U ↔ ∃ (V : Opens (X default)), IsCompact V.1 ∧ f default '' V.1 = U := by
  refine ⟨fun ⟨s, hs, V, hc, hcov⟩ ↦ ?_, fun ⟨V, hc, h⟩ ↦ ?_⟩
  · cases s.eq_empty_or_singleton_of_unique <;> aesop
  · refine ⟨{default}, Set.finite_singleton _, fun i h ↦ h ▸ V, fun i ↦ ?_, by simpa⟩
    rintro rfl
    simpa
/-
**IsCompactOpenCovered.id_iff_isOpen_and_isCompact** 是 Mathlib 中的一个引理，位于命名空间 `Is
CompactOpenCovered`。
形式化陈述：id_iff_isOpen_and_isCompact [TopologicalSpace S] : IsCompactOpenCovered (f
un _ : Unit => id) U ↔ IsOpen U ∧ IsCompact U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsCompactOpenCovered.iff_of_unique`：iff_of_unique [Unique ι] : IsCompact
OpenCovered f U ↔ exists (V : Opens (X default)), IsCompact V.1 ∧ f default '' V
.1 = U
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma id_iff_isOpen_and_isCompact [TopologicalSpace S] :
    IsCompactOpenCovered (fun _ : Unit ↦ id) U ↔ IsOpen U ∧ IsCompact U := by
  rw [iff_of_unique]
  refine ⟨fun ⟨V, hV, heq⟩ ↦ ?_, fun ⟨ho, hc⟩ ↦ ⟨⟨U, ho⟩, hc, by simp⟩⟩
  simp only [id_eq, Set.image_id', carrier_eq_coe, ← heq] at heq ⊢
  exact ⟨V.2, hV⟩
/-
**IsCompactOpenCovered.iff_isCompactOpenCovered_sigmaMk** 是 Mathlib 中的一个引理，位于命名空
间 `IsCompactOpenCovered`。
形式化陈述：iff_isCompactOpenCovered_sigmaMk : IsCompactOpenCovered f U ↔ IsCompactOpe
nCovered (fun (_ : Unit) (p : Σ i : ι, X i) => f p.1 p.2) U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsCompactOpenCovered.iff_of_unique`：iff_of_unique [Unique ι] : IsCompact
OpenCovered f U ↔ exists (V : Opens (X default)), IsCompact V.1 ∧ f default '' V
.1 = U
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_sigma_iff`：isOpen_sigma_iff {s : Set (Sigma σ)} : IsOpen s ↔ fora
ll i, IsOpen (Sigma.mk i ⁻¹' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.mk_preimage_sigma`：mk_preimage_sigma (hi : i in s) : Sigma.mk i ⁻¹' 
s.sigma t = t i
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Set.mk_preimage_sigma_eq_empty`：mk_preimage_sigma_eq_empty (hi : i ∉ s) 
: Sigma.mk i ⁻¹' s.sigma t = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Set.isCompact_sigma`：Set.isCompact_sigma {X : ι -> Type*} [forall i, Top
ologicalSpace (X i)] {s : Set ι} {t : forall i, Set (X i)} (hs : s.Finite) (ht :
 forall i…
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `IsCompact.sigma_exists_finite_sigma_eq`：IsCompact.sigma_exists_finite_si
gma_eq {X : ι -> Type*} [forall i, TopologicalSpace (X i)] (u : Set (Σ i, X i)) 
(hu : IsCompact u) : exists …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 35 条，此处仅展示前 30 条）
-/
lemma iff_isCompactOpenCovered_sigmaMk :
    IsCompactOpenCovered f U ↔
      IsCompactOpenCovered (fun (_ : Unit) (p : Σ i : ι, X i) ↦ f p.1 p.2) U := by
  classical
  rw [iff_of_unique (ι := Unit)]
  refine ⟨fun ⟨s, hs, V, hc, hU⟩ ↦ ?_, fun ⟨V, hc, heq⟩ ↦ ?_⟩
  · refine ⟨⟨s.sigma fun i ↦ if h : i ∈ s then V i h else ∅, isOpen_sigma_iff.mpr ?_⟩, ?_, ?_⟩
    · intro i
      by_cases h : i ∈ s
      · simpa [h] using (V _ _).2
      · simp [h]
    · dsimp only
      exact Set.isCompact_sigma hs fun i ↦ (by simp_all)
    · aesop
  · obtain ⟨s, t, hs, hc, heq'⟩ := hc.sigma_exists_finite_sigma_eq
    have (i : ι) (hi : i ∈ s) : IsOpen (t i) := by
      rw [← Set.mk_preimage_sigma (t := t) hi]
      exact isOpen_sigma_iff.mp (heq' ▸ V.2) i
    refine ⟨s, hs, fun i hi ↦ ⟨t i, this i hi⟩, fun i _ ↦ hc i, ?_⟩
    simp_rw [coe_mk, ← heq, ← heq', Set.image_sigma_eq_iUnion, Function.comp_apply]
/-
**IsCompactOpenCovered.of_iUnion_eq_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `IsCompa
ctOpenCovered`。
形式化陈述：of_iUnion_eq_of_finite {κ : Type*} [Finite κ] (s : κ -> Set S) (hs : ⋃ i, 
s i = U) (H : forall i, IsCompactOpenCovered f (s i)) : IsCompactOpenCovered f U
参数：s : κ -> Set S；hs : ⋃ i, s i = U；H : forall i, IsCompactOpenCovered f (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsCompactOpenCovered.iff_isCompactOpenCovered_sigmaMk`：iff_isCompactOpen
Covered_sigmaMk : IsCompactOpenCovered f U ↔ IsCompactOpenCovered (fun (_ : Unit
) (p : Σ i : ι, X i) => f p.1 p.2) U
· 使用引理 `IsCompactOpenCovered.iff_of_unique`：iff_of_unique [Unique ι] : IsCompact
OpenCovered f U ↔ exists (V : Opens (X default)), IsCompact V.1 ∧ f default '' V
.1 = U
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `isCompact_iUnion`：isCompact_iUnion {ι : Sort*} {f : ι -> Set X} [Finite 
ι] (h : forall i, IsCompact (f i)) : IsCompact (⋃ i, f i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma of_iUnion_eq_of_finite {κ : Type*} [Finite κ] (s : κ → Set S) (hs : ⋃ i, s i = U)
    (H : ∀ i, IsCompactOpenCovered f (s i)) : IsCompactOpenCovered f U := by
  rw [iff_isCompactOpenCovered_sigmaMk, iff_of_unique]
  have (i : κ) : ∃ (V : Opens (Σ i, X i)), IsCompact V.1 ∧ (f _ ·.snd) '' V.1 = s i := by
    convert! H i; rw [iff_isCompactOpenCovered_sigmaMk, iff_of_unique]
  choose V hVeq hVc using this
  exact ⟨⨆ i, V i, by simpa using isCompact_iUnion hVeq, by simp_all [Set.image_iUnion, ← hs]⟩
/-
**IsCompactOpenCovered.of_biUnion_eq_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `IsComp
actOpenCovered`。
形式化陈述：of_biUnion_eq_of_finite (s : Set (Set S)) (hs : ⋃ t in s, t = U) (hf : s.F
inite) (H : forall t in s, IsCompactOpenCovered f t) : IsCompactOpenCovered f U
参数：s : Set (Set S)；hs : ⋃ t in s, t = U；hf : s.Finite；H : forall t in s, IsCompa
ctOpenCovered f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用引理 `IsCompactOpenCovered.of_iUnion_eq_of_finite`：of_iUnion_eq_of_finite {κ :
 Type*} [Finite κ] (s : κ -> Set S) (hs : ⋃ i, s i = U) (H : forall i, IsCompact
OpenCovered f (s i)) : IsCompactO…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
lemma of_biUnion_eq_of_finite (s : Set (Set S)) (hs : ⋃ t ∈ s, t = U) (hf : s.Finite)
    (H : ∀ t ∈ s, IsCompactOpenCovered f t) : IsCompactOpenCovered f U := by
  have := hf.to_subtype
  exact of_iUnion_eq_of_finite (fun i : s ↦ i.1) (by simpa) (by simpa)
/-
**IsCompactOpenCovered.of_biUnion_eq_of_isCompact** 是 Mathlib 中的一个引理，位于命名空间 `IsC
ompactOpenCovered`。
形式化陈述：of_biUnion_eq_of_isCompact [TopologicalSpace S] {U : Set S} (hU : IsCompac
t U) (s : Set (Opens S)) (hs : ⋃ t in s, t = U) (H : forall t in s, IsCompactOpe
nCovered f t) : IsCompactOpenCovered f U
参数：hU : IsCompact U；s : Set (Opens S)；hs : ⋃ t in s, t = U；H : forall t in s, Is
CompactOpenCovered f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `IsCompactOpenCovered.of_biUnion_eq_of_finite`：of_biUnion_eq_of_finite (s
 : Set (Set S)) (hs : ⋃ t in s, t = U) (hf : s.Finite) (H : forall t in s, IsCom
pactOpenCovered f t) : IsCompactOp…
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biUnion_and'`：biUnion_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iUnion_iUnion_eq_right`：iUnion_iUnion_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋃ (x) (h : b = x), s x h = s b rfl
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma of_biUnion_eq_of_isCompact [TopologicalSpace S] {U : Set S} (hU : IsCompact U)
    (s : Set (Opens S)) (hs : ⋃ t ∈ s, t = U) (H : ∀ t ∈ s, IsCompactOpenCovered f t) :
    IsCompactOpenCovered f U := by
  classical
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun V : s ↦ V.1) (fun V ↦ V.1.2) (by simp [← hs])
  refine of_biUnion_eq_of_finite (SetLike.coe '' (t.image Subtype.val : Set (Opens S))) ?_ ?_ ?_
  · exact subset_antisymm (fun x h ↦ by aesop) (subset_trans ht <| by simp)
  · exact Set.toFinite _
  · grind
/-
**IsCompactOpenCovered.of_isCompact_of_forall_exists_isCompactOpenCovered** 是 Ma
thlib 中的一个引理，位于命名空间 `IsCompactOpenCovered`。
形式化陈述：of_isCompact_of_forall_exists_isCompactOpenCovered [TopologicalSpace S] {U
 : Set S} (hU : IsCompact U) (H : forall x in U, exists t subseteq U, x in t ∧ I
sOpen t ∧ IsCompactOpenCovered f t) : IsCompactOpenCovered f U
参数：hU : IsCompact U；H : forall x in U, exists t subseteq U, x in t ∧ IsOpen t ∧ 
IsCompactOpenCovered f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompactOpenCovered.of_biUnion_eq_of_isCompact`：of_biUnion_eq_of_isComp
act [TopologicalSpace S] {U : Set S} (hU : IsCompact U) (s : Set (Opens S)) (hs 
: ⋃ t in s, t = U) (H : forall t in s…
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma of_isCompact_of_forall_exists_isCompactOpenCovered [TopologicalSpace S] {U : Set S}
    (hU : IsCompact U) (H : ∀ x ∈ U, ∃ t ⊆ U, x ∈ t ∧ IsOpen t ∧ IsCompactOpenCovered f t) :
    IsCompactOpenCovered f U := by
  choose Us hU' hUx hUo hU'' using H
  refine of_biUnion_eq_of_isCompact hU { Us x h | (x : S) (h : x ∈ U) } ?_ ?_
  · refine subset_antisymm (fun x ↦ ?_) fun x hx ↦ ?_
    · simp [Opens.forall]
      grind
    · simpa using ⟨⟨Us x hx, hUo _ _⟩, ⟨x, by simpa⟩, hUx _ _⟩
  · grind
/-
**IsCompactOpenCovered.image** 是 Mathlib 中的一个引理，位于命名空间 `IsCompactOpenCovered`。
形式化陈述：image {i : ι} (V : Opens (X i)) (hV : IsCompact (X
参数：V : Opens (X i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma image {i : ι} (V : Opens (X i)) (hV : IsCompact (X := X i) V) :
    IsCompactOpenCovered f (f i '' V) := by
  refine ⟨{i}, Set.finite_singleton i, fun j hj ↦ hj ▸ V, by rintro i rfl; simpa, by simp⟩
/-
**IsCompactOpenCovered.of_finite** 是 Mathlib 中的一个引理，位于命名空间 `IsCompactOpenCovered
`。
形式化陈述：of_finite {U : Set S} {κ : Type*} [Finite κ] (a : κ -> ι) (V : forall k, O
pens (X (a k))) (hV : forall k, IsCompact (V k).1) (hU : ⋃ k, f (a k) '' V k = U
) : IsCompactOpenCovered f U
参数：a : κ -> ι；V : forall k, Opens (X (a k))；hV : forall k, IsCompact (V k).1；hU 
: ⋃ k, f (a k) '' V k = U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompactOpenCovered.of_iUnion_eq_of_finite`：of_iUnion_eq_of_finite {κ :
 Type*} [Finite κ] (s : κ -> Set S) (hs : ⋃ i, s i = U) (H : forall i, IsCompact
OpenCovered f (s i)) : IsCompactO…
· 使用引理 `IsCompactOpenCovered.image`：image {i : ι} (V : Opens (X i)) (hV : IsComp
act (X
-/
lemma of_finite {U : Set S} {κ : Type*} [Finite κ] (a : κ → ι) (V : ∀ k, Opens (X (a k)))
    (hV : ∀ k, IsCompact (V k).1) (hU : ⋃ k, f (a k) '' V k = U) :
    IsCompactOpenCovered f U :=
  of_iUnion_eq_of_finite _ hU (fun _ ↦ .image _ (hV _))

set_option backward.isDefEq.respectTransparency false in
/-- If `U` is compact-open covered and the `X i` have a basis of compact opens,
`U` can be written as the union of images of elements of the basis. -/
/-
**IsCompactOpenCovered.exists_mem_of_isBasis** 是 Mathlib 中的一个引理，位于命名空间 `IsCompac
tOpenCovered`。
形式化陈述：exists_mem_of_isBasis {B : forall i, Set (Opens (X i))} (hB : forall i, Is
Basis (B i)) (hBc : forall (i : ι), forall U in B i, IsCompact U.1) {U : Set S} 
(hU : IsCompactOpenCovered f U) : exists (n : Nat) (a : Fin n -> ι) (V : forall 
i, Opens (X (a i))), (forall i, V i in B (a i)) ∧ ⋃ i, f (a i) '' V i = U
参数：Opens (X i)；hB : forall i, IsBasis (B i)；hBc : forall (i : ι), forall U in B 
i, IsCompact U.1；hU : IsCompactOpenCovered f U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finite.instSigma`：∀ {α : Type u_1} {β : α → Type u_2} [Finite α] [∀ (a :
 α), Finite (β a)], Finite ((a : α) × β a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `TopologicalSpace.Opens.coe_sSup`：coe_sSup {S : Set (Opens α)} : (↑(sSup 
S) : Set α) = ⋃ i in S, ↑i
· 使用定理 `TopologicalSpace.Opens.IsBasis.exists_finite_of_isCompact`：∀ {α : Type u
_2} [inst : TopologicalSpace α] {B : Set (TopologicalSpace.Opens α)},   Topologi
calSpace.Opens.IsBasis B →     ∀ {U : Topologic…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Surjective.iUnion_comp`：iUnion_comp {f : ι -> ι₂} (hf : Surject
ive f) (g : ι₂ -> Set α) : ⋃ x, g (f x) = ⋃ y, g y
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `U` is compact-open covered and the `X i` have a basis of compact opens,
`U` can be written as the union of images of elements of the basis.
-/
lemma exists_mem_of_isBasis {B : ∀ i, Set (Opens (X i))} (hB : ∀ i, IsBasis (B i))
    (hBc : ∀ (i : ι), ∀ U ∈ B i, IsCompact U.1)
    {U : Set S} (hU : IsCompactOpenCovered f U) :
    ∃ (n : ℕ) (a : Fin n → ι) (V : ∀ i, Opens (X (a i))),
      (∀ i, V i ∈ B (a i)) ∧ ⋃ i, f (a i) '' V i = U := by
  suffices h : ∃ (κ : Type _) (_ : Finite κ) (a : κ → ι) (V : ∀ i, Opens (X (a i))),
      (∀ i, V i ∈ B (a i)) ∧ (∀ i, IsCompact (V i).1) ∧ ⋃ i, f (a i) '' V i = U by
    obtain ⟨κ, _, a, V, hB, hc, hU⟩ := h
    cases nonempty_fintype κ
    refine ⟨Fintype.card κ, a ∘ (Fintype.equivFin κ).symm, fun i ↦ V _, fun i ↦ hB _, ?_⟩
    simp [← hU, ← (Fintype.equivFin κ).symm.surjective.iUnion_comp, Function.comp_apply]
  obtain ⟨s, hs, V, hc, hunion⟩ := hU
  choose Us UsB hUsf hUs using fun i : s ↦ (hB i.1).exists_finite_of_isCompact (hc i i.2)
  let σ := Σ i : s, Us i
  have : Finite s := hs
  have (i : _) : Finite (Us i) := hUsf i
  refine ⟨σ, inferInstance, fun i ↦ i.1.1, fun i ↦ i.2.1, fun i ↦ UsB _ (by simp),
      fun _ ↦ hBc _ _ (UsB _ (by simp)), ?_⟩
  rw [← hunion]
  ext x
  simp_rw [Set.mem_iUnion]
  refine ⟨fun ⟨i, hi, o, ho⟩ ↦ by aesop, fun ⟨i, hi, h, hmem, heq⟩ ↦ ?_⟩
  rw [hUs ⟨i, hi⟩, coe_sSup, Set.mem_iUnion] at hmem
  obtain ⟨a, ha⟩ := hmem
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at ha
  use ⟨⟨i, hi⟩, ⟨a, ha.1⟩⟩, h, ha.2, heq
/-
**IsCompactOpenCovered.of_finite_of_isSpectralMap** 是 Mathlib 中的一个引理，位于命名空间 `IsC
ompactOpenCovered`。
形式化陈述：of_finite_of_isSpectralMap [Finite ι] [TopologicalSpace S] (hf : forall i,
 IsSpectralMap (f i)) {U : Set S} (hs : forall x in U, exists i, x in Set.range 
(f i)) (hU : IsOpen U) (hc : IsCompact U) : IsCompactOpenCovered f U
参数：hf : forall i, IsSpectralMap (f i)；hs : forall x in U, exists i, x in Set.ran
ge (f i)；hU : IsOpen U；hc : IsCompact U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `IsSpectralMap.toContinuous`：∀ {α : Type u_2} {β : Type u_3} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β},   IsSpectralMap f → C
ontinuous f
· 使用定理 `IsCompact.preimage_of_isOpen`：IsCompact.preimage_of_isOpen (hf : IsSpect
ralMap f) (h₀ : IsCompact s) (h₁ : IsOpen s) : IsCompact (f ⁻¹' s)
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma of_finite_of_isSpectralMap [Finite ι] [TopologicalSpace S]
    (hf : ∀ i, IsSpectralMap (f i)) {U : Set S} (hs : ∀ x ∈ U, ∃ i, x ∈ Set.range (f i))
    (hU : IsOpen U) (hc : IsCompact U) :
    IsCompactOpenCovered f U := by
  refine ⟨.univ, Set.finite_univ, fun i _ ↦ ⟨f i ⁻¹' U, hU.preimage (hf i).1⟩,
    fun i _ ↦ hc.preimage_of_isOpen (hf i) hU, subset_antisymm (by simp) fun x hx ↦ ?_⟩
  obtain ⟨i, y, rfl⟩ := hs x hx
  simpa using ⟨i, y, hx, rfl⟩
/-
**IsCompactOpenCovered.of_isOpenMap** 是 Mathlib 中的一个引理，位于命名空间 `IsCompactOpenCove
red`。
形式化陈述：of_isOpenMap [TopologicalSpace S] [forall i, PrespectralSpace (X i)] (hfc 
: forall i, Continuous (f i)) (h : forall i, IsOpenMap (f i)) {U : Set S} (hs : 
forall x in U, exists i, x in Set.range (f i)) (hU : IsOpen U) (hc : IsCompact U
) : IsCompactOpenCovered f U
参数：X i；hfc : forall i, Continuous (f i)；h : forall i, IsOpenMap (f i)；hs : foral
l x in U, exists i, x in Set.range (f i)；hU : IsOpen U；hc : IsCompact U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsCompactOpenCovered.iff_isCompactOpenCovered_sigmaMk`：iff_isCompactOpen
Covered_sigmaMk : IsCompactOpenCovered f U ↔ IsCompactOpenCovered (fun (_ : Unit
) (p : Σ i : ι, X i) => f p.1 p.2) U
· 使用引理 `IsCompactOpenCovered.iff_of_unique`：iff_of_unique [Unique ι] : IsCompact
OpenCovered f U ↔ exists (V : Opens (X default)), IsCompact V.1 ∧ f default '' V
.1 = U
· 使用引理 `IsOpenMap.exists_opens_image_eq_of_prespectralSpace`：IsOpenMap.exists_op
ens_image_eq_of_prespectralSpace [PrespectralSpace X] {f : X -> Y} (hfc : Contin
uous f) (h : IsOpenMap f) {U : Set Y} (hs…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_sigma_iff`：continuous_sigma_iff {f : Sigma σ -> X} : Continuo
us f ↔ forall i, Continuous fun a => f ⟨i, a⟩
· 使用定理 `isOpenMap_sigma`：isOpenMap_sigma {f : Sigma σ -> X} : IsOpenMap f ↔ fora
ll i, IsOpenMap fun a => f ⟨i, a⟩
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma of_isOpenMap [TopologicalSpace S] [∀ i, PrespectralSpace (X i)]
    (hfc : ∀ i, Continuous (f i)) (h : ∀ i, IsOpenMap (f i))
    {U : Set S} (hs : ∀ x ∈ U, ∃ i, x ∈ Set.range (f i)) (hU : IsOpen U) (hc : IsCompact U) :
    IsCompactOpenCovered f U := by
  rw [iff_isCompactOpenCovered_sigmaMk, iff_of_unique]
  refine (isOpenMap_sigma.mpr h).exists_opens_image_eq_of_prespectralSpace
      (continuous_sigma_iff.mpr hfc) (fun x hx ↦ ?_) hU hc
  simpa using hs x hx

/-- Being compact open covered descends along refinements if the spaces are prespectral. -/
/-
**IsCompactOpenCovered.of_comp** 是 Mathlib 中的一个引理，位于命名空间 `IsCompactOpenCovered`。
形式化陈述：of_comp [forall i, PrespectralSpace (X i)] [TopologicalSpace S] {σ : Type*
} {Y : σ -> Type*} [forall i, TopologicalSpace (Y i)] (g : forall i, Y i -> S) {
a : σ -> ι} (t : forall i, Y i -> X (a i)) (ht : forall i, Continuous (t i)) (hg
e : forall i, g i = f (a i) ∘ t i) (hf : forall i, Continuous (f i)) {U : Set S}
 (ho : IsOpen U) (hU : IsCompactOpenCovered g U) : IsCompactOpenCovered f U
参数：X i；Y i；g : forall i, Y i -> S；t : forall i, Y i -> X (a i)；ht : forall i, Co
ntinuous (t i)；hge : forall i, g i = f (a i) ∘ t i；hf : forall i, Continuous (f 
i)；ho : IsOpen U；hU : IsCompactOpenCovered g U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsCompactOpenCovered.iff_isCompactOpenCovered_sigmaMk`：iff_isCompactOpen
Covered_sigmaMk : IsCompactOpenCovered f U ↔ IsCompactOpenCovered (fun (_ : Unit
) (p : Σ i : ι, X i) => f p.1 p.2) U
· 使用引理 `IsCompactOpenCovered.iff_of_unique`：iff_of_unique [Unique ι] : IsCompact
OpenCovered f U ↔ exists (V : Opens (X default)), IsCompact V.1 ∧ f default '' V
.1 = U
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Continuous.sigma_map`：Continuous.sigma_map {f₁ : ι -> κ} {f₂ : forall i,
 σ i -> τ (f₁ i)} (hf : forall i, Continuous (f₂ i)) : Continuous (Sigma.map f₁ 
f₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `PrespectralSpace.exists_isCompact_and_isOpen_between`：PrespectralSpace.e
xists_isCompact_and_isOpen_between [PrespectralSpace X] {K U : Set X} (hK : IsCo
mpact K) (hU : IsOpen U) (hKU : K subseteq…
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t

--- 原说明 ---
Being compact open covered descends along refinements if the spaces are prespect
ral.
-/
lemma of_comp [∀ i, PrespectralSpace (X i)] [TopologicalSpace S]
    {σ : Type*} {Y : σ → Type*} [∀ i, TopologicalSpace (Y i)]
    (g : ∀ i, Y i → S) {a : σ → ι} (t : ∀ i, Y i → X (a i)) (ht : ∀ i, Continuous (t i))
    (hge : ∀ i, g i = f (a i) ∘ t i)
    (hf : ∀ i, Continuous (f i)) {U : Set S} (ho : IsOpen U) (hU : IsCompactOpenCovered g U) :
    IsCompactOpenCovered f U := by
  rw [iff_isCompactOpenCovered_sigmaMk, iff_of_unique] at hU ⊢
  let p : (Σ i, Y i) → (Σ i, X i) := Sigma.map a t
  have hcomp : (fun x ↦ f x.1 x.2) ∘ p = fun x ↦ g x.1 x.2 := by
    ext
    simp [hge, p, Sigma.map]
  have hp : Continuous p := Continuous.sigma_map ht
  have hf : Continuous (fun p : Σ i, X i ↦ f p.1 p.2) := by simp [hf]
  obtain ⟨V, hV, heq⟩ := hU
  obtain ⟨K, hK, ho, hVK, hKU⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
      (hV.image hp) (ho.preimage hf) <| by
    simp [← heq, ← Set.preimage_comp, hcomp, Set.subset_preimage_image]
  refine ⟨⟨K, ho⟩, hK, subset_antisymm (by simpa) ?_⟩
  rw [← heq, ← hcomp, Set.image_comp]
  exact subset_trans (Set.image_mono hVK) (by simp)

end IsCompactOpenCovered

