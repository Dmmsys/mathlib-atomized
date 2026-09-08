/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Floris van Doorn, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.Lift
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The filter of small sets

This file defines the filter of small sets w.r.t. a filter `f`, which is the largest filter
containing all powersets of members of `f`.

`g` converges to `f.smallSets` if for all `s ∈ f`, eventually we have `g x ⊆ s`.

An example usage is that if `f : ι → E → ℝ` is a family of nonnegative functions with integral 1,
then saying that `fun i ↦ support (f i)` tendsto `(𝓝 0).smallSets` is a way of saying that
`f` tends to the Dirac delta distribution.
-/

assert_not_exists Set.Finite

@[expose] public section

open Filter

open Set

variable {α β : Type*} {ι : Sort*}

namespace Filter

variable {l l' la : Filter α} {lb : Filter β}

/-- The filter `l.smallSets` is the largest filter containing all powersets of members of `l`. -/
/-
**Filter.smallSets** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：smallSets (l : Filter α) : Filter (Set α)
参数：l : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)

--- 原说明 ---
The filter `l.smallSets` is the largest filter containing all powersets of membe
rs of `l`.
-/
def smallSets (l : Filter α) : Filter (Set α) :=
  l.lift' powerset
/-
**Filter.smallSets_eq_generate** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：smallSets_eq_generate {f : Filter α} : f.smallSets = generate (powerset ''
 f.sets)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.generate_eq_biInf`：generate_eq_biInf (S : Set (Set α)) : generate
 S = ⨅ s in S, 𝓟 s
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `iInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
γ : Type u_8} {f : β → γ} {g : γ → α} {t : Set β},   ⨅ c ∈ f '' t, g c = ⨅ b ∈ t
…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smallSets_eq_generate {f : Filter α} : f.smallSets = generate (powerset '' f.sets) := by
  simp_rw [generate_eq_biInf, smallSets, iInf_image, Filter.lift', Filter.lift, Function.comp_apply,
    Filter.mem_sets]

-- TODO: get more properties from the adjunction?
-- TODO: is there a general way to get a lower adjoint for the lift of an upper adjoint?
/-
**Filter.bind_smallSets_gc** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bind_smallSets_gc : GaloisConnection (fun L : Filter (Set α) => L.bind pri
ncipal) smallSets
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.smallSets_eq_generate`：smallSets_eq_generate {f : Filter α} : f.s
mallSets = generate (powerset '' f.sets)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem bind_smallSets_gc :
    GaloisConnection (fun L : Filter (Set α) ↦ L.bind principal) smallSets := by
  intro L l
  simp_rw [smallSets_eq_generate, le_generate_iff, image_subset_iff]
  rfl
/-
**Filter.HasBasis.smallSets** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_3} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → l.smallSets.HasBasis p fun i => 𝒫 s i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.lift'`：Filter.HasBasis.lift'_interior {l : Filter X} {p 
: ι -> Prop} {s : ι -> Set X} (h : l.HasBasis p s) : (l.lift' interior).HasBasis
 p fun i =>…
· 使用定理 `Set.monotone_powerset`：monotone_powerset : Monotone (powerset : Set α ->
 Set (Set α))
-/
protected theorem HasBasis.smallSets {p : ι → Prop} {s : ι → Set α} (h : HasBasis l p s) :
    HasBasis l.smallSets p fun i => 𝒫 s i :=
  h.lift' monotone_powerset
/-
**Filter.hasBasis_smallSets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_smallSets (l : Filter α) : HasBasis l.smallSets (fun t : Set α =>
 t in l) powerset
参数：l : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.smallSets`：∀ {α : Type u_1} {ι : Sort u_3} {l : Filter α
} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l.smallSets.HasBasis p fun 
i => 𝒫 s i
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem hasBasis_smallSets (l : Filter α) :
    HasBasis l.smallSets (fun t : Set α => t ∈ l) powerset :=
  l.basis_sets.smallSets
/-
**Filter.Eventually.exists_mem_basis_of_smallSets** 是 Mathlib 中的一个定理，位于命名空间 `Fil
ter.Eventually`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_3} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α} {P : Set α → Prop},   (∀ᶠ (t : Set α) in l.smallSets, P t) → l.HasBasis p s 
→ ∃ i, p i ∧ P (s i)
参数：∀ᶠ (t : Set α) in l.smallSets, P t；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Filter.HasBasis.smallSets`：∀ {α : Type u_1} {ι : Sort u_3} {l : Filter α
} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l.smallSets.HasBasis p fun 
i => 𝒫 s i
-/
theorem Eventually.exists_mem_basis_of_smallSets {p : ι → Prop} {s : ι → Set α} {P : Set α → Prop}
    (h₁ : ∀ᶠ t in l.smallSets, P t) (h₂ : HasBasis l p s) : ∃ i, p i ∧ P (s i) :=
  (h₂.smallSets.eventually_iff.mp h₁).imp fun _i ⟨hpi, hi⟩ ↦ ⟨hpi, hi Subset.rfl⟩
/-
**Filter.Frequently.smallSets_of_forall_mem_basis** 是 Mathlib 中的一个定理，位于命名空间 `Fil
ter.Frequently`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_3} {l : Filter α} {p : ι → Prop} {s : ι → Set
 α} {P : Set α → Prop},   (∀ (i : ι), p i → P (s i)) → l.HasBasis p s → ∃ᶠ (t : 
Set α) in l.smallSets, P t
参数：∀ (i : ι), p i → P (s i)；t : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.frequently_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∃ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Filter.HasBasis.smallSets`：∀ {α : Type u_1} {ι : Sort u_3} {l : Filter α
} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l.smallSets.HasBasis p fun 
i => 𝒫 s i
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem Frequently.smallSets_of_forall_mem_basis {p : ι → Prop} {s : ι → Set α} {P : Set α → Prop}
    (h₁ : ∀ i, p i → P (s i)) (h₂ : HasBasis l p s) : ∃ᶠ t in l.smallSets, P t :=
  h₂.smallSets.frequently_iff.mpr fun _ hi => ⟨_, Subset.rfl, h₁ _ hi⟩
/-
**Filter.Eventually.exists_mem_of_smallSets** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Ev
entually`。
形式化陈述：∀ {α : Type u_1} {l : Filter α} {p : Set α → Prop}, (∀ᶠ (t : Set α) in l.s
mallSets, p t) → ∃ s ∈ l, p s
参数：∀ᶠ (t : Set α) in l.smallSets, p t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists_mem_basis_of_smallSets`：∀ {α : Type u_1} {ι : S
ort u_3} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {P : Set α → Prop},   (∀ᶠ
 (t : Set α) in l.smallSets, P t) → l…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem Eventually.exists_mem_of_smallSets {p : Set α → Prop}
    (h : ∀ᶠ t in l.smallSets, p t) : ∃ s ∈ l, p s :=
  h.exists_mem_basis_of_smallSets l.basis_sets

/-! No `Frequently.smallSets_of_forall_mem (h : ∀ s ∈ l, p s) : ∃ᶠ t in l.smallSets, p t` as
`Filter.frequently_smallSets_mem : ∃ᶠ t in l.smallSets, t ∈ l` is preferred. -/

/-- `g` converges to `f.smallSets` if for all `s ∈ f`, eventually we have `g x ⊆ s`. -/
/-
**Filter.tendsto_smallSets_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_smallSets_iff {f : α -> Set β} : Tendsto f la lb.smallSets ↔ foral
l t in lb, forallᶠ x in la, f x subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Filter.hasBasis_smallSets`：hasBasis_smallSets (l : Filter α) : HasBasis 
l.smallSets (fun t : Set α => t in l) powerset

--- 原说明 ---
`g` converges to `f.smallSets` if for all `s ∈ f`, eventually we have `g x ⊆ s`.
-/
theorem tendsto_smallSets_iff {f : α → Set β} :
    Tendsto f la lb.smallSets ↔ ∀ t ∈ lb, ∀ᶠ x in la, f x ⊆ t :=
  (hasBasis_smallSets lb).tendsto_right_iff
/-
**Filter.eventually_smallSets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_smallSets {p : Set α -> Prop} : (forallᶠ s in l.smallSets, p s)
 ↔ exists s in l, forall t, t subseteq s -> p t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_lift'_iff`：∀ {α : Type u_1} {β : Type u_2} {f : Filter
 α} {h : Set α → Set β},   Monotone h → ∀ {p : β → Prop}, (∀ᶠ (y : β) in f.lift'
 h, p y) ↔ ∃ t ∈ …
· 使用定理 `Set.monotone_powerset`：monotone_powerset : Monotone (powerset : Set α ->
 Set (Set α))
-/
theorem eventually_smallSets {p : Set α → Prop} :
    (∀ᶠ s in l.smallSets, p s) ↔ ∃ s ∈ l, ∀ t, t ⊆ s → p t :=
  eventually_lift'_iff monotone_powerset
/-
**Filter.eventually_smallSets'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_smallSets' {p : Set α -> Prop} (hp : forall ⦃s t⦄, s subseteq t
 -> p t -> p s) : (forallᶠ s in l.smallSets, p s) ↔ exists s in l, p s
参数：hp : forall ⦃s t⦄, s subseteq t -> p t -> p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.eventually_smallSets`：eventually_smallSets {p : Set α -> Prop} : 
(forallᶠ s in l.smallSets, p s) ↔ exists s in l, forall t, t subseteq s -> p t
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem eventually_smallSets' {p : Set α → Prop} (hp : ∀ ⦃s t⦄, s ⊆ t → p t → p s) :
    (∀ᶠ s in l.smallSets, p s) ↔ ∃ s ∈ l, p s :=
  eventually_smallSets.trans <|
    exists_congr fun s => Iff.rfl.and ⟨fun H => H s Subset.rfl, fun hs _t ht => hp ht hs⟩
/-
**Filter.HasBasis.eventually_smallSets** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasi
s`。
形式化陈述：∀ {α : Type u_4} {ι : Sort u_5} {p : ι → Prop} {l : Filter α} {s : ι → Set
 α} {q : Set α → Prop} {hl : l.HasBasis p s},   (∀ ⦃s t : Set α⦄, s ⊆ t → q t → 
q s) → ((∀ᶠ (s : Set α) in l.smallSets, q s) ↔ ∃ i, p i ∧ q (s i))
参数：∀ ⦃s t : Set α⦄, s ⊆ t → q t → q s；(∀ᶠ (s : Set α) in l.smallSets, q s) ↔ ∃ i
, p i ∧ q (s i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_smallSets'`：eventually_smallSets' {p : Set α -> Prop} 
(hp : forall ⦃s t⦄, s subseteq t -> p t -> p s) : (forallᶠ s in l.smallSets, p s
) ↔ exists s in l,…
· 使用定理 `Filter.HasBasis.exists_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {P : Set α → Prop}, (∀ ⦃
s t : Set α⦄, s …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem HasBasis.eventually_smallSets {α : Type*} {ι : Sort*} {p : ι → Prop} {l : Filter α}
    {s : ι → Set α} {q : Set α → Prop} {hl : l.HasBasis p s}
    (hq : ∀ ⦃s t : Set α⦄, s ⊆ t → q t → q s) :
    (∀ᶠ s in l.smallSets, q s) ↔ ∃ i, p i ∧ q (s i) := by
  rw [l.eventually_smallSets' hq, hl.exists_iff hq]
/-
**Filter.frequently_smallSets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_smallSets {p : Set α -> Prop} : (existsᶠ s in l.smallSets, p s)
 ↔ forall t in l, exists s, s subseteq t ∧ p s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.frequently_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∃ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Filter.hasBasis_smallSets`：hasBasis_smallSets (l : Filter α) : HasBasis 
l.smallSets (fun t : Set α => t in l) powerset
-/
theorem frequently_smallSets {p : Set α → Prop} :
    (∃ᶠ s in l.smallSets, p s) ↔ ∀ t ∈ l, ∃ s, s ⊆ t ∧ p s :=
  l.hasBasis_smallSets.frequently_iff
/-
**Filter.frequently_smallSets_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_smallSets_mem (l : Filter α) : existsᶠ s in l.smallSets, s in l
参数：l : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.frequently_smallSets`：frequently_smallSets {p : Set α -> Prop} : 
(existsᶠ s in l.smallSets, p s) ↔ forall t in l, exists s, s subseteq t ∧ p s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem frequently_smallSets_mem (l : Filter α) : ∃ᶠ s in l.smallSets, s ∈ l :=
  frequently_smallSets.2 fun t ht => ⟨t, Subset.rfl, ht⟩
/-
**Filter.frequently_smallSets'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_smallSets' {α : Type*} {l : Filter α} {p : Set α -> Prop} (hp :
 forall ⦃s t : Set α⦄, s subseteq t -> p s -> p t) : (existsᶠ s in l.smallSets, 
p s) ↔ forall t in l, p t
参数：hp : forall ⦃s t : Set α⦄, s subseteq t -> p s -> p t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Filter.eventually_smallSets'`：eventually_smallSets' {p : Set α -> Prop} 
(hp : forall ⦃s t⦄, s subseteq t -> p t -> p s) : (forallᶠ s in l.smallSets, p s
) ↔ exists s in l,…
-/
theorem frequently_smallSets' {α : Type*} {l : Filter α} {p : Set α → Prop}
    (hp : ∀ ⦃s t : Set α⦄, s ⊆ t → p s → p t) :
    (∃ᶠ s in l.smallSets, p s) ↔ ∀ t ∈ l, p t := by
  convert! not_iff_not.mpr <| l.eventually_smallSets' (p := (¬p ·)) (by tauto)
  simp
/-
**Filter.HasBasis.frequently_smallSets** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasi
s`。
形式化陈述：∀ {α : Type u_4} {ι : Sort u_5} {p : ι → Prop} {l : Filter α} {s : ι → Set
 α} {q : Set α → Prop} {hl : l.HasBasis p s},   (∀ ⦃s t : Set α⦄, s ⊆ t → q s → 
q t) → ((∃ᶠ (s : Set α) in l.smallSets, q s) ↔ ∀ (i : ι), p i → q (s i))
参数：∀ ⦃s t : Set α⦄, s ⊆ t → q s → q t；(∃ᶠ (s : Set α) in l.smallSets, q s) ↔ ∀ (
i : ι), p i → q (s i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.frequently_smallSets'`：frequently_smallSets' {α : Type*} {l : Fil
ter α} {p : Set α -> Prop} (hp : forall ⦃s t : Set α⦄, s subseteq t -> p s -> p 
t) : (existsᶠ s in…
· 使用定理 `Filter.HasBasis.forall_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s →     ∀ {P : Set α → Prop}, 
(∀ ⦃s t : Set α⦄…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem HasBasis.frequently_smallSets {α : Type*} {ι : Sort*} {p : ι → Prop} {l : Filter α}
    {s : ι → Set α} {q : Set α → Prop} {hl : l.HasBasis p s}
    (hq : ∀ ⦃s t : Set α⦄, s ⊆ t → q s → q t) :
    (∃ᶠ s in l.smallSets, q s) ↔ ∀ i, p i → q (s i) := by
  rw [Filter.frequently_smallSets' hq, hl.forall_iff hq]

@[simp]
/-
**Filter.tendsto_image_smallSets** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_image_smallSets {f : α -> β} : Tendsto (f '' ·) la.smallSets lb.sm
allSets ↔ Tendsto f la lb
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_smallSets_iff`：tendsto_smallSets_iff {f : α -> Set β} : T
endsto f la lb.smallSets ↔ forall t in lb, forallᶠ x in la, f x subseteq t
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Filter.eventually_smallSets'`：eventually_smallSets' {p : Set α -> Prop} 
(hp : forall ⦃s t⦄, s subseteq t -> p t -> p s) : (forallᶠ s in l.smallSets, p s
) ↔ exists s in l,…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma tendsto_image_smallSets {f : α → β} :
    Tendsto (f '' ·) la.smallSets lb.smallSets ↔ Tendsto f la lb := by
  rw [tendsto_smallSets_iff]
  refine forall₂_congr fun u hu ↦ ?_
  rw [eventually_smallSets' fun s t hst ht ↦ (image_mono hst).trans ht]
  simp only [image_subset_iff, exists_mem_subset_iff, mem_map]

alias ⟨_, Tendsto.image_smallSets⟩ := tendsto_image_smallSets
/-
**Filter.HasAntitoneBasis.tendsto_smallSets** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Ha
sAntitoneBasis`。
形式化陈述：∀ {α : Type u_1} {l : Filter α} {ι : Type u_4} [inst : Preorder ι] {s : ι 
→ Set α},   l.HasAntitoneBasis s → Filter.Tendsto s Filter.atTop l.smallSets
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_smallSets_iff`：tendsto_smallSets_iff {f : α -> Set β} : T
endsto f la lb.smallSets ↔ forall t in lb, forallᶠ x in la, f x subseteq t
· 使用定理 `Filter.HasAntitoneBasis.eventually_subset`：∀ {ι : Type u_1} {α : Type u_
3} [inst : Preorder ι] {l : Filter α} {s : ι → Set α},   l.HasAntitoneBasis s → 
∀ {t : Set α}, t ∈ l → ∀ᶠ (i : …
-/
theorem HasAntitoneBasis.tendsto_smallSets {ι} [Preorder ι] {s : ι → Set α}
    (hl : l.HasAntitoneBasis s) : Tendsto s atTop l.smallSets :=
  tendsto_smallSets_iff.2 fun _t ht => hl.eventually_subset ht

@[gcongr, mono]
/-
**Filter.monotone_smallSets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：monotone_smallSets : Monotone (@smallSets α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.monotone_lift'`：monotone_lift' [Preorder γ] {f : γ -> Filter α} {
g : γ -> Set α -> Set β} (hf : Monotone f) (hg : Monotone g) : Monotone fun c =>
 (f c).lift…
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
· 使用定理 `monotone_const`：monotone_const [Preorder α] [Preorder β] {c : β} : Monot
one fun _ : α => c
-/
theorem monotone_smallSets : Monotone (@smallSets α) :=
  monotone_lift' monotone_id monotone_const

@[simp]
/-
**Filter.smallSets_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：smallSets_bot : (⊥ : Filter α).smallSets = pure ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.smallSets.eq_1`：∀ {α : Type u_1} (l : Filter α), l.smallSets = l.
lift' Set.powerset
· 使用定理 `Filter.lift'_bot`：∀ {α : Type u_1} {β : Type u_2} {h : Set α → Set β}, M
onotone h → ⊥.lift' h = Filter.principal (h ∅)
· 使用定理 `Set.monotone_powerset`：monotone_powerset : Monotone (powerset : Set α ->
 Set (Set α))
· 使用定理 `Set.powerset_empty`：powerset_empty : 𝒫 (∅ : Set α) = {∅}
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
-/
theorem smallSets_bot : (⊥ : Filter α).smallSets = pure ∅ := by
  rw [smallSets, lift'_bot, powerset_empty, principal_singleton]
  exact monotone_powerset

@[simp]
/-
**Filter.smallSets_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：smallSets_top : (⊤ : Filter α).smallSets = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.smallSets.eq_1`：∀ {α : Type u_1} (l : Filter α), l.smallSets = l.
lift' Set.powerset
· 使用定理 `Filter.lift'_top`：∀ {α : Type u_1} {β : Type u_2} (h : Set α → Set β), ⊤
.lift' h = Filter.principal (h Set.univ)
· 使用定理 `Set.powerset_univ`：powerset_univ : 𝒫 (univ : Set α) = univ
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
-/
theorem smallSets_top : (⊤ : Filter α).smallSets = ⊤ := by
  rw [smallSets, lift'_top, powerset_univ, principal_univ]

@[simp]
/-
**Filter.smallSets_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：smallSets_principal (s : Set α) : (𝓟 s).smallSets = 𝓟 (𝒫 s)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'_principal`：∀ {α : Type u_1} {β : Type u_2} {h : Set α → Set
 β} {s : Set α},   Monotone h → (Filter.principal s).lift' h = Filter.principal 
(h s)
· 使用定理 `Set.monotone_powerset`：monotone_powerset : Monotone (powerset : Set α ->
 Set (Set α))
-/
theorem smallSets_principal (s : Set α) : (𝓟 s).smallSets = 𝓟 (𝒫 s) :=
  lift'_principal monotone_powerset
/-
**Filter.smallSets_comap_eq_comap_image** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：smallSets_comap_eq_comap_image (l : Filter β) (f : α -> β) : (comap f l).s
mallSets = comap (image f) l.smallSets
参数：l : Filter β；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_comm_of_l_comm`：u_comm_of_l_comm {X : Type*} [Partial
Order X] {Y : Type*} [Preorder Y] {Z : Type*} [Preorder Z] {W : Type*} [Preorder
 W] {lYX : X -> Y} {uXY…
· 使用定理 `Filter.gc_map_comap`：gc_map_comap (m : α -> β) : GaloisConnection (map m
) (comap m)
· 使用定理 `Filter.bind_smallSets_gc`：bind_smallSets_gc : GaloisConnection (fun L : 
Filter (Set α) => L.bind principal) smallSets
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.map_principal`：map_principal {s : Set α} {f : α -> β} : map f (𝓟 
s) = 𝓟 (Set.image f s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem smallSets_comap_eq_comap_image (l : Filter β) (f : α → β) :
    (comap f l).smallSets = comap (image f) l.smallSets := by
  refine (gc_map_comap _).u_comm_of_l_comm (gc_map_comap _) bind_smallSets_gc bind_smallSets_gc ?_
  simp [Function.comp_def, map_bind, bind_map]
/-
**Filter.smallSets_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：smallSets_comap (l : Filter β) (f : α -> β) : (comap f l).smallSets = l.li
ft' (powerset ∘ preimage f)
参数：l : Filter β；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_lift'_eq2`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
f : Filter α} {m : β → α} {g : Set β → Set γ},   Monotone g → (Filter.comap m f)
.lift' g = f…
· 使用定理 `Set.monotone_powerset`：monotone_powerset : Monotone (powerset : Set α ->
 Set (Set α))
-/
theorem smallSets_comap (l : Filter β) (f : α → β) :
    (comap f l).smallSets = l.lift' (powerset ∘ preimage f) :=
  comap_lift'_eq2 monotone_powerset
/-
**Filter.comap_smallSets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_smallSets (l : Filter β) (f : α -> Set β) : comap f l.smallSets = l.
lift' (preimage f ∘ powerset)
参数：l : Filter β；f : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_lift'_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {h : Set α → Set β} {m : γ → β},   Filter.comap m (f.lift' h) = f.l
ift' (Set.p…
-/
theorem comap_smallSets (l : Filter β) (f : α → Set β) :
    comap f l.smallSets = l.lift' (preimage f ∘ powerset) :=
  comap_lift'_eq
/-
**Filter.smallSets_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：smallSets_iInf {f : ι -> Filter α} : (iInf f).smallSets = ⨅ i, (f i).small
Sets
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'_iInf_of_map_univ`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort
 u_4} {f : ι → Filter α} {g : Set α → Set β},   (∀ {s t : Set α}, g (s ∩ t) = g 
s ∩ g t) → g Set.un…
· 使用定理 `Set.powerset_inter`：powerset_inter (s t : Set α) : 𝒫 (s inter t) = 𝒫 s i
nter 𝒫 t
· 使用定理 `Set.powerset_univ`：powerset_univ : 𝒫 (univ : Set α) = univ
-/
theorem smallSets_iInf {f : ι → Filter α} : (iInf f).smallSets = ⨅ i, (f i).smallSets :=
  lift'_iInf_of_map_univ (powerset_inter _ _) powerset_univ
/-
**Filter.smallSets_inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：smallSets_inf (l₁ l₂ : Filter α) : (l₁ ⊓ l₂).smallSets = l₁.smallSets ⊓ l₂
.smallSets
参数：l₁ l₂ : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'_inf`：∀ {α : Type u_1} {β : Type u_2} (f g : Filter α) {s : 
Set α → Set β},   (∀ (t₁ t₂ : Set α), s (t₁ ∩ t₂) = s t₁ ∩ s t₂) → (f ⊓ g).lift'
 s = f…
· 使用定理 `Set.powerset_inter`：powerset_inter (s t : Set α) : 𝒫 (s inter t) = 𝒫 s i
nter 𝒫 t
-/
theorem smallSets_inf (l₁ l₂ : Filter α) : (l₁ ⊓ l₂).smallSets = l₁.smallSets ⊓ l₂.smallSets :=
  lift'_inf _ _ powerset_inter
/-
**Filter.smallSets_neBot** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：smallSets_neBot (l : Filter α) : NeBot l.smallSets
参数：l : Filter α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.lift'_neBot_iff`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {
h : Set α → Set β},   Monotone h → ((f.lift' h).NeBot ↔ ∀ s ∈ f, (h s).Nonempty)
· 使用定理 `Set.monotone_powerset`：monotone_powerset : Monotone (powerset : Set α ->
 Set (Set α))
· 使用定理 `Set.powerset_nonempty`：powerset_nonempty : (𝒫 s).Nonempty
-/
instance smallSets_neBot (l : Filter α) : NeBot l.smallSets := by
  refine (lift'_neBot_iff ?_).2 fun _ _ => powerset_nonempty
  exact monotone_powerset
/-
**Filter.Tendsto.smallSets_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {lb : Filter β} {s t : α →
 Set β},   Filter.Tendsto t la lb.smallSets → (∀ᶠ (x : α) in la, s x ⊆ t x) → Fi
lter.Tendsto s la lb.smallSets
参数：∀ᶠ (x : α) in la, s x ⊆ t x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_smallSets_iff`：tendsto_smallSets_iff {f : α -> Set β} : T
endsto f la lb.smallSets ↔ forall t in lb, forallᶠ x in la, f x subseteq t
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem Tendsto.smallSets_mono {s t : α → Set β} (ht : Tendsto t la lb.smallSets)
    (hst : ∀ᶠ x in la, s x ⊆ t x) : Tendsto s la lb.smallSets := by
  rw [tendsto_smallSets_iff] at ht ⊢
  exact fun u hu => (ht u hu).mp (hst.mono fun _ hst ht => hst.trans ht)

/-- Generalized **squeeze theorem** (also known as **sandwich theorem**). If `s : α → Set β` is a
family of sets that tends to `Filter.smallSets lb` along `la` and `f : α → β` is a function such
that `f x ∈ s x` eventually along `la`, then `f` tends to `lb` along `la`.

If `s x` is the closed interval `[g x, h x]` for some functions `g`, `h` that tend to the same limit
`𝓝 y`, then we obtain the standard squeeze theorem, see
`tendsto_of_tendsto_of_tendsto_of_le_of_le'`. -/
/-
**Filter.Tendsto.of_smallSets** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {lb : Filter β} {s : α → S
et β} {f : α → β},   Filter.Tendsto s la lb.smallSets → (∀ᶠ (x : α) in la, f x ∈
 s x) → Filter.Tendsto f la lb
参数：∀ᶠ (x : α) in la, f x ∈ s x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_smallSets_iff`：tendsto_smallSets_iff {f : α -> Set β} : T
endsto f la lb.smallSets ↔ forall t in lb, forallᶠ x in la, f x subseteq t

--- 原说明 ---
Generalized **squeeze theorem** (also known as **sandwich theorem**). If `s : α 
→ Set β` is a
family of sets that tends to `Filter.smallSets lb` along `la` and `f : α → β` is
 a function such
that `f x ∈ s x` eventually along `la`, then `f` tends to `lb` along `la`.

If `s x` is the closed interval `[g x, h x]` for some functions `g`, `h` that te
nd to the same limit
`𝓝 y`, then we obtain the standard squeeze theorem, see
`tendsto_of_tendsto_of_tendsto_of_le_of_le'`.
-/
theorem Tendsto.of_smallSets {s : α → Set β} {f : α → β} (hs : Tendsto s la lb.smallSets)
    (hf : ∀ᶠ x in la, f x ∈ s x) : Tendsto f la lb := fun t ht =>
  hf.mp <| (tendsto_smallSets_iff.mp hs t ht).mono fun _ h₁ h₂ => h₁ h₂

@[simp]
/-
**Filter.eventually_smallSets_eventually** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_smallSets_eventually {p : α -> Prop} : (forallᶠ s in l.smallSet
s, forallᶠ x in l', x in s -> p x) ↔ forallᶠ x in l ⊓ l', p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_smallSets'`：eventually_smallSets' {p : Set α -> Prop} 
(hp : forall ⦃s t⦄, s subseteq t -> p t -> p s) : (forallᶠ s in l.smallSets, p s
) ↔ exists s in l,…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem eventually_smallSets_eventually {p : α → Prop} :
    (∀ᶠ s in l.smallSets, ∀ᶠ x in l', x ∈ s → p x) ↔ ∀ᶠ x in l ⊓ l', p x :=
  calc
    _ ↔ ∃ s ∈ l, ∀ᶠ x in l', x ∈ s → p x :=
      eventually_smallSets' fun _ _ hst ht => ht.mono fun _ hx hs => hx (hst hs)
    _ ↔ ∃ s ∈ l, ∃ t ∈ l', ∀ x, x ∈ t → x ∈ s → p x := by simp only [eventually_iff_exists_mem]
    _ ↔ ∀ᶠ x in l ⊓ l', p x := by simp only [eventually_inf, and_comm, mem_inter_iff, ← and_imp]

@[simp]
/-
**Filter.eventually_smallSets_forall** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_smallSets_forall {p : α -> Prop} : (forallᶠ s in l.smallSets, f
orall x in s, p x) ↔ forallᶠ x in l, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
· 使用定理 `Filter.eventually_smallSets_eventually`：eventually_smallSets_eventually 
{p : α -> Prop} : (forallᶠ s in l.smallSets, forallᶠ x in l', x in s -> p x) ↔ f
orallᶠ x in l ⊓ l', p x
-/
theorem eventually_smallSets_forall {p : α → Prop} :
    (∀ᶠ s in l.smallSets, ∀ x ∈ s, p x) ↔ ∀ᶠ x in l, p x := by
  simpa only [inf_top_eq, eventually_top] using @eventually_smallSets_eventually α l ⊤ p

alias ⟨Eventually.of_smallSets, Eventually.smallSets⟩ := eventually_smallSets_forall

@[simp]
/-
**Filter.eventually_smallSets_subset** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_smallSets_subset {s : Set α} : (forallᶠ t in l.smallSets, t sub
seteq s) ↔ s in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_smallSets_forall`：eventually_smallSets_forall {p : α -
> Prop} : (forallᶠ s in l.smallSets, forall x in s, p x) ↔ forallᶠ x in l, p x
-/
theorem eventually_smallSets_subset {s : Set α} : (∀ᶠ t in l.smallSets, t ⊆ s) ↔ s ∈ l :=
  eventually_smallSets_forall

end Filter

