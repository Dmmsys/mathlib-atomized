/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alex Kontorovich
-/
module

public import Mathlib.Data.Set.Piecewise
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Filter.Bases.Finite

/-!
# (Co)product of a family of filters

In this file we prove some basic properties of two filters on `Π i, α i`.

* `Filter.pi (f : Π i, Filter (α i))` to be the maximal filter on `Π i, α i` such that
  `∀ i, Filter.Tendsto (Function.eval i) (Filter.pi f) (f i)`. It is defined as
  `Π i, Filter.comap (Function.eval i) (f i)`. This is a generalization of binary products to
  indexed products.

* `Filter.coprodᵢ (f : Π i, Filter (α i))`: a generalization of `Filter.coprod`; it is the supremum
  of `comap (eval i) (f i)`.
-/

@[expose] public section


open Set Function Filter

namespace Filter

variable {ι : Type*} {α : ι → Type*} {f f₁ f₂ : (i : ι) → Filter (α i)} {s : (i : ι) → Set (α i)}
  {p : ∀ i, α i → Prop}

section Pi

/-
**Filter.tendsto_eval_pi** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_eval_pi (f : forall i, Filter (α i)) (i : ι) : Tendsto (eval i) (p
i f) (f i)
参数：f : forall i, Filter (α i)；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_iInf'`：tendsto_iInf' {f : α -> β} {x : ι -> Filter α} {y 
: Filter β} (i : ι) (hi : Tendsto f (x i) y) : Tendsto f (⨅ i, x i) y
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
-/
theorem tendsto_eval_pi (f : ∀ i, Filter (α i)) (i : ι) : Tendsto (eval i) (pi f) (f i) :=
  tendsto_iInf' i tendsto_comap
/-
**Filter.tendsto_pi** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_pi {β : Type*} {m : β -> forall i, α i} {l : Filter β} : Tendsto m
 l (pi f) ↔ forall i, Tendsto (fun x => m x i) l (f i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_pi {β : Type*} {m : β → ∀ i, α i} {l : Filter β} :
    Tendsto m l (pi f) ↔ ∀ i, Tendsto (fun x => m x i) l (f i) := by
  simp only [pi, tendsto_iInf, tendsto_comap_iff]; rfl

/-- If a function tends to a product `Filter.pi f` of filters, then its `i`-th component tends to
`f i`. See also `Filter.Tendsto.apply_nhds` for the special case of converging to a point in a
product of topological spaces. -/
alias ⟨Tendsto.apply, _⟩ := tendsto_pi

/-
**Filter.le_pi** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_pi {g : Filter (forall i, α i)} : g <= pi f ↔ forall i, Tendsto (eval i
) g (f i)
参数：forall i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_pi`：tendsto_pi {β : Type*} {m : β -> forall i, α i} {l : 
Filter β} : Tendsto m l (pi f) ↔ forall i, Tendsto (fun x => m x i) l (f i)
-/
theorem le_pi {g : Filter (∀ i, α i)} : g ≤ pi f ↔ ∀ i, Tendsto (eval i) g (f i) :=
  tendsto_pi

@[gcongr, mono]
/-
**Filter.pi_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pi_mono (h : forall i, f₁ i <= f₂ i) : pi f₁ <= pi f₂
参数：h : forall i, f₁ i <= f₂ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `Filter.comap_mono`：comap_mono : Monotone (comap m)
-/
theorem pi_mono (h : ∀ i, f₁ i ≤ f₂ i) : pi f₁ ≤ pi f₂ :=
  iInf_mono fun i => comap_mono <| h i
/-
**Filter.mem_pi_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_pi_of_mem (i : ι) {s : Set (α i)} (hs : s in f i) : eval i ⁻¹' s in pi
 f
参数：i : ι；α i；hs : s in f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_iInf_of_mem`：mem_iInf_of_mem {f : ι -> Filter α} (i : ι) {s} 
(hs : s in f i) : s in ⨅ i, f i
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
-/
theorem mem_pi_of_mem (i : ι) {s : Set (α i)} (hs : s ∈ f i) : eval i ⁻¹' s ∈ pi f :=
  mem_iInf_of_mem i <| preimage_mem_comap hs
/-
**Filter.pi_mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pi_mem_pi {I : Set ι} (hI : I.Finite) (h : forall i in I, s i in f i) : I.
pi s in pi f
参数：hI : I.Finite；h : forall i in I, s i in f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pi_def`：pi_def (i : Set α) (s : forall a, Set (π a)) : pi i s = ⋂ a 
in i, eval a ⁻¹' s a
· 使用定理 `Set.biInter_eq_iInter`：biInter_eq_iInter (s : Set α) (t : forall x in s,
 Set β) : ⋂ x in s, t x ‹_› = ⋂ x : s, t x x.2
· 使用定理 `Filter.mem_iInf_of_iInter`：mem_iInf_of_iInter {ι} {s : ι -> Filter α} {U
 : Set α} {I : Set ι} (I_fin : I.Finite) {V : I -> Set α} (hV : forall (i : I), 
V i in s i) (hU…
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem pi_mem_pi {I : Set ι} (hI : I.Finite) (h : ∀ i ∈ I, s i ∈ f i) : I.pi s ∈ pi f := by
  rw [pi_def, biInter_eq_iInter]
  refine mem_iInf_of_iInter hI (fun i => ?_) Subset.rfl
  exact preimage_mem_comap (h i i.2)
/-
**Filter.mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_pi {s : Set (forall i, α i)} : s in pi f ↔ exists I : Set ι, I.Finite 
∧ exists t : forall i, Set (α i), (forall i, t i in f i) ∧ I.pi t subseteq s
参数：forall i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.pi_def`：pi_def (i : Set α) (s : forall a, Set (π a)) : pi i s = ⋂ a 
in i, eval a ⁻¹' s a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.iInter₂_mono`：iInter₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋂ (i) (j), s i j subseteq ⋂ (i) (j), t i j
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.pi_mem_pi`：pi_mem_pi {I : Set ι} (hI : I.Finite) (h : forall i in
 I, s i in f i) : I.pi s in pi f
-/
theorem mem_pi {s : Set (∀ i, α i)} :
    s ∈ pi f ↔ ∃ I : Set ι, I.Finite ∧ ∃ t : ∀ i, Set (α i), (∀ i, t i ∈ f i) ∧ I.pi t ⊆ s := by
  constructor
  · simp only [pi, mem_iInf', mem_comap, pi_def]
    rintro ⟨I, If, V, hVf, -, rfl, -⟩
    choose t htf htV using hVf
    exact ⟨I, If, t, htf, iInter₂_mono fun i _ => htV i⟩
  · rintro ⟨I, If, t, htf, hts⟩
    exact mem_of_superset (pi_mem_pi If fun i _ => htf i) hts
/-
**Filter.mem_pi'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_pi' {s : Set (forall i, α i)} : s in pi f ↔ exists I : Finset ι, exist
s t : forall i, Set (α i), (forall i, t i in f i) ∧ Set.pi (↑I) t subseteq s
参数：forall i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.mem_pi`：mem_pi {s : Set (forall i, α i)} : s in pi f ↔ exists I :
 Set ι, I.Finite ∧ exists t : forall i, Set (α i), (forall i, t i in f i) ∧ I.pi
 t …
· 使用定理 `Set.exists_finite_iff_finset`：exists_finite_iff_finset {p : Set α -> Pro
p} : (exists s : Set α, s.Finite ∧ p s) ↔ exists s : Finset α, p ↑s
-/
theorem mem_pi' {s : Set (∀ i, α i)} :
    s ∈ pi f ↔ ∃ I : Finset ι, ∃ t : ∀ i, Set (α i), (∀ i, t i ∈ f i) ∧ Set.pi (↑I) t ⊆ s :=
  mem_pi.trans exists_finite_iff_finset
/-
**Filter.mem_of_pi_mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_of_pi_mem_pi [forall i, NeBot (f i)] {I : Set ι} (h : I.pi s in pi f) 
{i : ι} (hi : i in I) : s i in f i
参数：f i；h : I.pi s in pi f；hi : i in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_pi`：mem_pi {s : Set (forall i, α i)} : s in pi f ↔ exists I :
 Set ι, I.Finite ∧ exists t : forall i, Set (α i), (forall i, t i in f i) ∧ I.pi
 t …
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem mem_of_pi_mem_pi [∀ i, NeBot (f i)] {I : Set ι} (h : I.pi s ∈ pi f) {i : ι} (hi : i ∈ I) :
    s i ∈ f i := by
  classical
  rcases mem_pi.1 h with ⟨I', -, t, htf, hts⟩
  refine mem_of_superset (htf i) fun x hx => ?_
  have : ∀ i, (t i).Nonempty := fun i => nonempty_of_mem (htf i)
  choose g hg using this
  have : update g i x ∈ I'.pi t := fun j _ => by
    rcases eq_or_ne j i with (rfl | hne) <;> simp [*]
  simpa using hts this i hi

@[simp]
/-
**Filter.pi_mem_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pi_mem_pi_iff [forall i, NeBot (f i)] {I : Set ι} (hI : I.Finite) : I.pi s
 in pi f ↔ forall i in I, s i in f i
参数：f i；hI : I.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_pi_mem_pi`：mem_of_pi_mem_pi [forall i, NeBot (f i)] {I : S
et ι} (h : I.pi s in pi f) {i : ι} (hi : i in I) : s i in f i
· 使用定理 `Filter.pi_mem_pi`：pi_mem_pi {I : Set ι} (hI : I.Finite) (h : forall i in
 I, s i in f i) : I.pi s in pi f
-/
theorem pi_mem_pi_iff [∀ i, NeBot (f i)] {I : Set ι} (hI : I.Finite) :
    I.pi s ∈ pi f ↔ ∀ i ∈ I, s i ∈ f i :=
  ⟨fun h _i hi => mem_of_pi_mem_pi h hi, pi_mem_pi hI⟩
/-
**Filter.Eventually.eval_pi** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} {f : (i : ι) → Filter (α i)} {p : (i :
 ι) → α i → Prop} {i : ι},   (∀ᶠ (x : α i) in f i, p i x) → ∀ᶠ (x : (i : ι) → α 
i) in Filter.pi f, p i (x i)
参数：i : ι；α i；i : ι；∀ᶠ (x : α i) in f i, p i x；x : (i : ι) → α i；x i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_eval_pi`：tendsto_eval_pi (f : forall i, Filter (α i)) (i 
: ι) : Tendsto (eval i) (pi f) (f i)
-/
theorem Eventually.eval_pi {i : ι} (hf : ∀ᶠ x : α i in f i, p i x) :
    ∀ᶠ x : ∀ i : ι, α i in pi f, p i (x i) := (tendsto_eval_pi _ _).eventually hf
/-
**Filter.eventually_pi** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_pi [Finite ι] (hf : forall i, forallᶠ x in f i, p i x) : forall
ᶠ x : forall i, α i in pi f, forall i, p i (x i)
参数：hf : forall i, forallᶠ x in f i, p i x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_all`：eventually_all {ι : Sort*} [Finite ι] {l} {p : ι 
-> α -> Prop} : (forallᶠ x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p 
i x
· 使用定理 `Filter.Eventually.eval_pi`：∀ {ι : Type u_1} {α : ι → Type u_2} {f : (i :
 ι) → Filter (α i)} {p : (i : ι) → α i → Prop} {i : ι},   (∀ᶠ (x : α i) in f i, 
p i x) → ∀ᶠ (x …
-/
theorem eventually_pi [Finite ι] (hf : ∀ i, ∀ᶠ x in f i, p i x) :
    ∀ᶠ x : ∀ i, α i in pi f, ∀ i, p i (x i) := eventually_all.2 fun _i => (hf _).eval_pi
/-
**Filter.hasBasis_pi** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_pi {ι' : ι -> Type*} {s : forall i, ι' i -> Set (α i)} {p : foral
l i, ι' i -> Prop} (h : forall i, (f i).HasBasis (p i) (s i)) : (pi f).HasBasis 
(fun If : Set ι × forall i, ι' i => If.1.Finite ∧ forall i in If.1, p i (If.2 i)
) fun If : Set ι × forall i, ι' i => If.1.pi fun i => s i If.2 i
参数：α i；h : forall i, (f i).HasBasis (p i) (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.pi_def`：pi_def (i : Set α) (s : forall a, Set (π a)) : pi i s = ⋂ a 
in i, eval a ⁻¹' s a
· 使用定理 `Filter.HasBasis.iInf'`：∀ {α : Type u_1} {ι : Type u_6} {ι' : ι → Type u_
7} {l : ι → Filter α} {p : (i : ι) → ι' i → Prop}   {s : (i : ι) → ι' i → Set α}
,   (∀ (i :…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
-/
theorem hasBasis_pi {ι' : ι → Type*} {s : ∀ i, ι' i → Set (α i)} {p : ∀ i, ι' i → Prop}
    (h : ∀ i, (f i).HasBasis (p i) (s i)) :
    (pi f).HasBasis (fun If : Set ι × ∀ i, ι' i => If.1.Finite ∧ ∀ i ∈ If.1, p i (If.2 i))
      fun If : Set ι × ∀ i, ι' i => If.1.pi fun i => s i <| If.2 i := by
  simpa [Set.pi_def] using! HasBasis.iInf' fun i => (h i).comap (eval i : (∀ j, α j) → α i)
/-
**Filter.hasBasis_pi_same_index** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_pi_same_index {κ : Type*} {p : κ -> Prop} {s : Π i : ι, κ -> Set 
(α i)} (h : forall i : ι, (f i).HasBasis p (s i)) (h_dir : forall I : Set ι, for
all k : ι -> κ, I.Finite -> (forall i in I, p (k i)) -> exists k₀, p k₀ ∧ forall
 i in I, s i k₀ subseteq s i (k i)) : (pi f).HasBasis (fun Ik : Set ι × κ => Ik.
1.Finite ∧ p Ik.2) (fun Ik => Ik.1.pi (fun i => s i Ik.2))
参数：α i；h : forall i : ι, (f i).HasBasis p (s i)；h_dir : forall I : Set ι, forall
 k : ι -> κ, I.Finite -> (forall i in I, p (k i)) -> exists k₀, p k₀ ∧ forall i 
in I, s i k₀ subseteq s i (k i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `Filter.hasBasis_pi`：hasBasis_pi {ι' : ι -> Type*} {s : forall i, ι' i ->
 Set (α i)} {p : forall i, ι' i -> Prop} (h : forall i, (f i).HasBasis (p i) (s 
i)) : (p…
· 使用定理 `Set.pi_mono`：pi_mono (h : forall i in s, t₁ i subseteq t₂ i) : pi s t₁ s
ubseteq pi s t₂
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
theorem hasBasis_pi_same_index {κ : Type*} {p : κ → Prop} {s : Π i : ι, κ → Set (α i)}
    (h : ∀ i : ι, (f i).HasBasis p (s i))
    (h_dir : ∀ I : Set ι, ∀ k : ι → κ, I.Finite → (∀ i ∈ I, p (k i)) →
      ∃ k₀, p k₀ ∧ ∀ i ∈ I, s i k₀ ⊆ s i (k i)) :
    (pi f).HasBasis (fun Ik : Set ι × κ ↦ Ik.1.Finite ∧ p Ik.2)
      (fun Ik ↦ Ik.1.pi (fun i ↦ s i Ik.2)) := by
  refine hasBasis_pi h |>.to_hasBasis ?_ ?_
  · rintro ⟨I, k⟩ ⟨hI, hk⟩
    rcases h_dir I k hI hk with ⟨k₀, hk₀, hk₀'⟩
    exact ⟨⟨I, k₀⟩, ⟨hI, hk₀⟩, Set.pi_mono hk₀'⟩
  · rintro ⟨I, k⟩ ⟨hI, hk⟩
    exact ⟨⟨I, fun _ ↦ k⟩, ⟨hI, fun _ _ ↦ hk⟩, subset_rfl⟩
/-
**Filter.HasBasis.pi_self** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {κ : Type u_4} {f : Filter α} {p : κ → Pro
p} {s : κ → Set α},   f.HasBasis p s → (Filter.pi fun x => f).HasBasis (fun Ik =
> Ik.1.Finite ∧ p Ik.2) fun Ik => Ik.1.pi fun x => s Ik.2
参数：Filter.pi fun x => f；fun Ik => Ik.1.Finite ∧ p Ik.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.hasBasis_pi_same_index`：hasBasis_pi_same_index {κ : Type*} {p : κ
 -> Prop} {s : Π i : ι, κ -> Set (α i)} (h : forall i : ι, (f i).HasBasis p (s i
)) (h_dir : forall …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.biInter_mem`：biInter_mem {β : Type v} {s : β -> Set α} {is : Set 
β} (hf : is.Finite) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.biInter_subset_of_mem`：biInter_subset_of_mem {s : Set α} {t : α -> S
et β} {x : α} (xs : x in s) : ⋂ x in s, t x subseteq t x
-/
theorem HasBasis.pi_self {α : Type*} {κ : Type*} {f : Filter α} {p : κ → Prop} {s : κ → Set α}
    (h : f.HasBasis p s) :
    (pi fun _ ↦ f).HasBasis (fun Ik : Set ι × κ ↦ Ik.1.Finite ∧ p Ik.2)
      (fun Ik ↦ Ik.1.pi (fun _ ↦ s Ik.2)) := by
  refine hasBasis_pi_same_index (fun _ ↦ h) (fun I k hI hk ↦ ?_)
  rcases h.mem_iff.mp (biInter_mem hI |>.mpr fun i hi ↦ h.mem_of_mem (hk i hi))
    with ⟨k₀, hk₀, hk₀'⟩
  exact ⟨k₀, hk₀, fun i hi ↦ hk₀'.trans (biInter_subset_of_mem hi)⟩
/-
**Filter.le_pi_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_pi_principal (s : (i : ι) -> Set (α i)) : 𝓟 (univ.pi s) <= pi fun i => 
𝓟 (s i)
参数：s : (i : ι) -> Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_pi`：le_pi {g : Filter (forall i, α i)} : g <= pi f ↔ forall i,
 Tendsto (eval i) g (f i)
· 使用定理 `Filter.tendsto_principal_principal`：tendsto_principal_principal {f : α -
> β} {s : Set α} {t : Set β} : Tendsto f (𝓟 s) (𝓟 t) ↔ forall a in s, f a in t
· 使用定理 `trivial`：True
-/
theorem le_pi_principal (s : (i : ι) → Set (α i)) :
    𝓟 (univ.pi s) ≤ pi fun i ↦ 𝓟 (s i) :=
  le_pi.2 fun i ↦ tendsto_principal_principal.2 fun _f hf ↦ hf i trivial

/-- The indexed product of finitely many principal filters
is the principal filter corresponding to the cylinder `Set.univ.pi s`.

If the index type is infinite, then `mem_pi_principal` and `hasBasis_pi_principal` may be useful. -/
@[simp]
/-
**Filter.pi_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pi_principal [Finite ι] (s : (i : ι) -> Set (α i)) : pi (fun i => 𝓟 (s i))
 = 𝓟 (univ.pi s)
参数：s : (i : ι) -> Set (α i)。
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
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Filter.iInf_principal'`：iInf_principal' {ι : Type w} [Finite ι] (f : ι -
> Set α) : ⨅ i, 𝓟 (f i) = 𝓟 (⋂ i, f i)
· 使用定理 `Set.pi_def`：pi_def (i : Set α) (s : forall a, Set (π a)) : pi i s = ⋂ a 
in i, eval a ⁻¹' s a
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_true`：iInter_true {s : True -> Set α} : iInter s = s trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The indexed product of finitely many principal filters
is the principal filter corresponding to the cylinder `Set.univ.pi s`.

If the index type is infinite, then `mem_pi_principal` and `hasBasis_pi_principa
l` may be useful.
-/
theorem pi_principal [Finite ι] (s : (i : ι) → Set (α i)) :
    pi (fun i ↦ 𝓟 (s i)) = 𝓟 (univ.pi s) := by
  simp [Filter.pi, Set.pi_def]

/-- The indexed product of a (possibly, infinite) family of principal filters
is generated by the finite `Set.pi` cylinders.

If the index type is finite, then the indexed product of principal filters
is a principal filter, see `pi_principal`. -/
/-
**Filter.mem_pi_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_pi_principal {t : Set ((i : ι) -> α i)} : t in pi (fun i => 𝓟 (s i)) ↔
 exists I : Set ι, I.Finite ∧ I.pi s subseteq t
参数：(i : ι) -> α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.hasBasis_pi`：hasBasis_pi {ι' : ι -> Type*} {s : forall i, ι' i ->
 Set (α i)} {p : forall i, ι' i -> Prop} (h : forall i, (f i).HasBasis (p i) (s 
i)) : (p…
· 使用定理 `Filter.hasBasis_principal`：hasBasis_principal (t : Set α) : (𝓟 t).HasBas
is (fun _ : Unit => True) fun _ => t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The indexed product of a (possibly, infinite) family of principal filters
is generated by the finite `Set.pi` cylinders.

If the index type is finite, then the indexed product of principal filters
is a principal filter, see `pi_principal`.
-/
theorem mem_pi_principal {t : Set ((i : ι) → α i)} :
    t ∈ pi (fun i ↦ 𝓟 (s i)) ↔ ∃ I : Set ι, I.Finite ∧ I.pi s ⊆ t :=
  (hasBasis_pi (fun i ↦ hasBasis_principal _)).mem_iff.trans <| by simp

/-- The indexed product of a (possibly, infinite) family of principal filters
is generated by the finite `Set.pi` cylinders.

If the index type is finite, then the indexed product of principal filters
is a principal filter, see `pi_principal`. -/
/-
**Filter.hasBasis_pi_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_pi_principal (s : (i : ι) -> Set (α i)) : HasBasis (pi fun i => 𝓟
 (s i)) Set.Finite (Set.pi · s)
参数：s : (i : ι) -> Set (α i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_pi_principal`：mem_pi_principal {t : Set ((i : ι) -> α i)} : t
 in pi (fun i => 𝓟 (s i)) ↔ exists I : Set ι, I.Finite ∧ I.pi s subseteq t

--- 原说明 ---
The indexed product of a (possibly, infinite) family of principal filters
is generated by the finite `Set.pi` cylinders.

If the index type is finite, then the indexed product of principal filters
is a principal filter, see `pi_principal`.
-/
theorem hasBasis_pi_principal (s : (i : ι) → Set (α i)) :
    HasBasis (pi fun i ↦ 𝓟 (s i)) Set.Finite (Set.pi · s) :=
  ⟨fun _ ↦ mem_pi_principal⟩

/-- The indexed product of finitely many pure filters `pure (f i)` is the pure filter `pure f`.

If the index type is infinite, then `mem_pi_pure` and `hasBasis_pi_pure` below may be useful. -/
@[simp]
/-
**Filter.pi_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pi_pure [Finite ι] (f : (i : ι) -> α i) : pi (pure <| f ·) = pure f
参数：f : (i : ι) -> α i。
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
· 使用定理 `Filter.pi_principal`：pi_principal [Finite ι] (s : (i : ι) -> Set (α i)) 
: pi (fun i => 𝓟 (s i)) = 𝓟 (univ.pi s)
· 使用定理 `Set.univ_pi_singleton`：univ_pi_singleton (f : forall i, α i) : (pi univ 
fun i => {f i}) = ({f} : Set (forall i, α i))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The indexed product of finitely many pure filters `pure (f i)` is the pure filte
r `pure f`.

If the index type is infinite, then `mem_pi_pure` and `hasBasis_pi_pure` below m
ay be useful.
-/
theorem pi_pure [Finite ι] (f : (i : ι) → α i) : pi (pure <| f ·) = pure f := by
  simp only [← principal_singleton, pi_principal, univ_pi_singleton]

/-- The indexed product of a (possibly, infinite) family of pure filters `pure (f i)`
is generated by the sets of functions that are equal to `f` on a finite set.

If the index type is finite, then the indexed product of pure filters is a pure filter,
see `pi_pure`. -/
/-
**Filter.mem_pi_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_pi_pure {f : (i : ι) -> α i} {s : Set ((i : ι) -> α i)} : s in pi (fun
 i => pure (f i)) ↔ exists I : Set ι, I.Finite ∧ forall g, (forall i in I, g i =
 f i) -> g in s
参数：i : ι；(i : ι) -> α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The indexed product of a (possibly, infinite) family of pure filters `pure (f i)
`
is generated by the sets of functions that are equal to `f` on a finite set.

If the index type is finite, then the indexed product of pure filters is a pure 
filter,
see `pi_pure`.
-/
theorem mem_pi_pure {f : (i : ι) → α i} {s : Set ((i : ι) → α i)} :
    s ∈ pi (fun i ↦ pure (f i)) ↔ ∃ I : Set ι, I.Finite ∧ ∀ g, (∀ i ∈ I, g i = f i) → g ∈ s := by
  simp only [← principal_singleton, mem_pi_principal]
  simp [subset_def]

/-- The indexed product of a (possibly, infinite) family of pure filters `pure (f i)`
is generated by the sets of functions that are equal to `f` on a finite set.

If the index type is finite, then the indexed product of pure filters is a pure filter,
see `pi_pure`. -/
/-
**Filter.hasBasis_pi_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_pi_pure (f : (i : ι) -> α i) : HasBasis (pi fun i => pure (f i)) 
Set.Finite (fun I => {g | forall i in I, g i = f i})
参数：f : (i : ι) -> α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_pi_pure`：mem_pi_pure {f : (i : ι) -> α i} {s : Set ((i : ι) -
> α i)} : s in pi (fun i => pure (f i)) ↔ exists I : Set ι, I.Finite ∧ forall g,
 (forall…

--- 原说明 ---
The indexed product of a (possibly, infinite) family of pure filters `pure (f i)
`
is generated by the sets of functions that are equal to `f` on a finite set.

If the index type is finite, then the indexed product of pure filters is a pure 
filter,
see `pi_pure`.
-/
theorem hasBasis_pi_pure (f : (i : ι) → α i) :
    HasBasis (pi fun i ↦ pure (f i)) Set.Finite (fun I ↦ {g | ∀ i ∈ I, g i = f i}) :=
  ⟨fun _ ↦ mem_pi_pure⟩

@[simp]
/-
**Filter.pi_inf_principal_univ_pi_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pi_inf_principal_univ_pi_eq_bot : pi f ⊓ 𝓟 (Set.pi univ s) = ⊥ ↔ exists i,
 f i ⊓ 𝓟 (s i) = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_univ_pi`：mem_univ_pi : f in pi univ t ↔ forall i, f i in t i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.mem_pi_of_mem`：mem_pi_of_mem (i : ι) {s : Set (α i)} (hs : s in f
 i) : eval i ⁻¹' s in pi f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `trivial`：True
-/
theorem pi_inf_principal_univ_pi_eq_bot :
    pi f ⊓ 𝓟 (Set.pi univ s) = ⊥ ↔ ∃ i, f i ⊓ 𝓟 (s i) = ⊥ := by
  constructor
  · simp only [inf_principal_eq_bot, mem_pi]
    contrapose!
    rintro (hsf : ∀ i, ∃ᶠ x in f i, x ∈ s i) I - t htf hts
    have : ∀ i, (s i ∩ t i).Nonempty := fun i => ((hsf i).and_eventually (htf i)).exists
    choose x hxs hxt using this
    exact hts (fun i _ => hxt i) (mem_univ_pi.2 hxs)
  · simp only [inf_principal_eq_bot]
    rintro ⟨i, hi⟩
    filter_upwards [mem_pi_of_mem i hi] with x using mt fun h => h i trivial

@[simp]
/-
**Filter.pi_inf_principal_pi_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pi_inf_principal_pi_eq_bot [forall i, NeBot (f i)] {I : Set ι} : pi f ⊓ 𝓟 
(Set.pi I s) = ⊥ ↔ exists i in I, f i ⊓ 𝓟 (s i) = ⊥
参数：f i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_pi_piecewise_univ`：univ_pi_piecewise_univ {ι : Type*} {α : ι ->
 Type*} (s : Set ι) (t : forall i, Set (α i)) [forall x, Decidable (x in s)] : p
i univ (s.piecew…
· 使用定理 `Filter.pi_inf_principal_univ_pi_eq_bot`：pi_inf_principal_univ_pi_eq_bot 
: pi f ⊓ 𝓟 (Set.pi univ s) = ⊥ ↔ exists i, f i ⊓ 𝓟 (s i) = ⊥
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem pi_inf_principal_pi_eq_bot [∀ i, NeBot (f i)] {I : Set ι} :
    pi f ⊓ 𝓟 (Set.pi I s) = ⊥ ↔ ∃ i ∈ I, f i ⊓ 𝓟 (s i) = ⊥ := by
  classical
  rw [← univ_pi_piecewise_univ I, pi_inf_principal_univ_pi_eq_bot]
  refine exists_congr fun i => ?_
  by_cases hi : i ∈ I <;> simp [hi, NeBot.ne']

@[simp]
/-
**Filter.pi_inf_principal_univ_pi_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pi_inf_principal_univ_pi_neBot : NeBot (pi f ⊓ 𝓟 (Set.pi univ s)) ↔ forall
 i, NeBot (f i ⊓ 𝓟 (s i))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pi_inf_principal_univ_pi_neBot :
    NeBot (pi f ⊓ 𝓟 (Set.pi univ s)) ↔ ∀ i, NeBot (f i ⊓ 𝓟 (s i)) := by simp [neBot_iff]

@[simp]
/-
**Filter.pi_inf_principal_pi_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pi_inf_principal_pi_neBot [forall i, NeBot (f i)] {I : Set ι} : NeBot (pi 
f ⊓ 𝓟 (I.pi s)) ↔ forall i in I, NeBot (f i ⊓ 𝓟 (s i))
参数：f i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pi_inf_principal_pi_neBot [∀ i, NeBot (f i)] {I : Set ι} :
    NeBot (pi f ⊓ 𝓟 (I.pi s)) ↔ ∀ i ∈ I, NeBot (f i ⊓ 𝓟 (s i)) := by simp [neBot_iff]
/-
**Filter.PiInfPrincipalPi.neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter.PiInfPrincipal
Pi`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} {f : (i : ι) → Filter (α i)} {s : (i :
 ι) → Set (α i)}   [h : ∀ (i : ι), (f i ⊓ Filter.principal (s i)).NeBot] {I : Se
t ι}, (Filter.pi f ⊓ Filter.principal (I.pi s)).NeBot
参数：i : ι；α i；i : ι；α i；i : ι；f i ⊓ Filter.principal (s i)；Filter.pi f ⊓ Filter.p
rincipal (I.pi s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.pi_inf_principal_univ_pi_neBot`：pi_inf_principal_univ_pi_neBot : 
NeBot (pi f ⊓ 𝓟 (Set.pi univ s)) ↔ forall i, NeBot (f i ⊓ 𝓟 (s i))
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
· 使用定理 `trivial`：True
-/
instance PiInfPrincipalPi.neBot [h : ∀ i, NeBot (f i ⊓ 𝓟 (s i))] {I : Set ι} :
    NeBot (pi f ⊓ 𝓟 (I.pi s)) :=
  (pi_inf_principal_univ_pi_neBot.2 ‹_›).mono <|
    inf_le_inf_left _ <| principal_mono.2 fun _ hx i _ => hx i trivial

@[simp]
/-
**Filter.pi_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pi_eq_bot : pi f = ⊥ ↔ exists i, f i = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.pi_univ`：pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = 
univ
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.pi_inf_principal_univ_pi_eq_bot`：pi_inf_principal_univ_pi_eq_bot 
: pi f ⊓ 𝓟 (Set.pi univ s) = ⊥ ↔ exists i, f i ⊓ 𝓟 (s i) = ⊥
-/
theorem pi_eq_bot : pi f = ⊥ ↔ ∃ i, f i = ⊥ := by
  simpa using @pi_inf_principal_univ_pi_eq_bot ι α f fun _ => univ

@[simp]
/-
**Filter.pi_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pi_neBot : NeBot (pi f) ↔ forall i, NeBot (f i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pi_neBot : NeBot (pi f) ↔ ∀ i, NeBot (f i) := by simp [neBot_iff]
/-
**Filter.** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, NeBot (f i)] : NeBot (pi f) :=
  pi_neBot.2 ‹_›

@[simp]
/-
**Filter.map_eval_pi** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_eval_pi (f : forall i, Filter (α i)) [forall i, NeBot (f i)] (i : ι) :
 map (eval i) (pi f) = f i
参数：f : forall i, Filter (α i)；f i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.tendsto_eval_pi`：tendsto_eval_pi (f : forall i, Filter (α i)) (i 
: ι) : Tendsto (eval i) (pi f) (f i)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_pi`：mem_pi {s : Set (forall i, α i)} : s in pi f ↔ exists I :
 Set ι, I.Finite ∧ exists t : forall i, Set (α i), (forall i, t i in f i) ∧ I.pi
 t …
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_eval_image_pi`：subset_eval_image_pi (ht : (s.pi t).Nonempty) 
(i : ι) : t i subseteq eval i '' s.pi t
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `Filter.instNeBotForallPi`：∀ {ι : Type u_1} {α : ι → Type u_2} {f : (i : 
ι) → Filter (α i)} [∀ (i : ι), (f i).NeBot], (Filter.pi f).NeBot
· 使用定理 `Filter.pi_mem_pi`：pi_mem_pi {I : Set ι} (hI : I.Finite) (h : forall i in
 I, s i in f i) : I.pi s in pi f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_eval_pi (f : ∀ i, Filter (α i)) [∀ i, NeBot (f i)] (i : ι) :
    map (eval i) (pi f) = f i := by
  refine le_antisymm (tendsto_eval_pi f i) fun s hs => ?_
  rcases mem_pi.1 (mem_map.1 hs) with ⟨I, hIf, t, htf, hI⟩
  rw [← image_subset_iff] at hI
  refine mem_of_superset (htf i) ((subset_eval_image_pi ?_ _).trans hI)
  exact nonempty_of_mem (pi_mem_pi hIf fun i _ => htf i)

@[simp]
/-
**Filter.pi_le_pi** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pi_le_pi [forall i, NeBot (f₁ i)] : pi f₁ <= pi f₂ ↔ forall i, f₁ i <= f₂ 
i
参数：f₁ i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Filter.tendsto_eval_pi`：tendsto_eval_pi (f : forall i, Filter (α i)) (i 
: ι) : Tendsto (eval i) (pi f) (f i)
· 使用定理 `Filter.map_eval_pi`：map_eval_pi (f : forall i, Filter (α i)) [forall i, 
NeBot (f i)] (i : ι) : map (eval i) (pi f) = f i
· 使用定理 `Filter.pi_mono`：pi_mono (h : forall i, f₁ i <= f₂ i) : pi f₁ <= pi f₂
-/
theorem pi_le_pi [∀ i, NeBot (f₁ i)] : pi f₁ ≤ pi f₂ ↔ ∀ i, f₁ i ≤ f₂ i :=
  ⟨fun h i => map_eval_pi f₁ i ▸ (tendsto_eval_pi _ _).mono_left h, pi_mono⟩

@[simp]
/-
**Filter.pi_inj** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pi_inj [forall i, NeBot (f₁ i)] : pi f₁ = pi f₂ ↔ f₁ = f₂
参数：f₁ i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.pi_le_pi`：pi_le_pi [forall i, NeBot (f₁ i)] : pi f₁ <= pi f₂ ↔ fo
rall i, f₁ i <= f₂ i
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Filter.neBot_of_le`：neBot_of_le {f g : Filter α} [hf : NeBot f] (hg : f 
<= g) : NeBot g
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem pi_inj [∀ i, NeBot (f₁ i)] : pi f₁ = pi f₂ ↔ f₁ = f₂ := by
  refine ⟨fun h => ?_, congr_arg pi⟩
  have hle : f₁ ≤ f₂ := pi_le_pi.1 h.le
  have : ∀ i, NeBot (f₂ i) := fun i => neBot_of_le (hle i)
  exact hle.antisymm (pi_le_pi.1 h.ge)
/-
**Filter.tendsto_piMap_pi** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_piMap_pi {β : ι -> Type*} {f : forall i, α i -> β i} {l : forall i
, Filter (α i)} {l' : forall i, Filter (β i)} (h : forall i, Tendsto (f i) (l i)
 (l' i)) : Tendsto (Pi.map f) (pi l) (pi l')
参数：α i；β i；h : forall i, Tendsto (f i) (l i) (l' i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_pi`：tendsto_pi {β : Type*} {m : β -> forall i, α i} {l : 
Filter β} : Tendsto m l (pi f) ↔ forall i, Tendsto (fun x => m x i) l (f i)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_eval_pi`：tendsto_eval_pi (f : forall i, Filter (α i)) (i 
: ι) : Tendsto (eval i) (pi f) (f i)
-/
theorem tendsto_piMap_pi {β : ι → Type*} {f : ∀ i, α i → β i} {l : ∀ i, Filter (α i)}
    {l' : ∀ i, Filter (β i)} (h : ∀ i, Tendsto (f i) (l i) (l' i)) :
    Tendsto (Pi.map f) (pi l) (pi l') :=
  tendsto_pi.2 fun i ↦ (h i).comp (tendsto_eval_pi _ _)
/-
**Filter.pi_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pi_comap {β : ι -> Type*} {f : forall i, α i -> β i} {l : forall i, Filter
 (β i)} : pi (fun i => comap (f i) (l i)) = comap (Pi.map f) (pi l)
参数：β i。
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
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Filter.comap_iInf`：comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) =
 ⨅ i, comap m (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pi_comap {β : ι → Type*} {f : ∀ i, α i → β i} {l : ∀ i, Filter (β i)} :
    pi (fun i ↦ comap (f i) (l i)) = comap (Pi.map f) (pi l) := by
  simp [Filter.pi, Filter.comap_comap, Function.comp_def]

end Pi

/-! ### `n`-ary coproducts of filters -/

section CoprodCat

-- for "Coprod"

/-- Coproduct of filters. -/
/-
**Filter.coprod** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Filter α → Filter β → Filter (α × β)
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coproduct of filters.
-/
protected def coprodᵢ (f : ∀ i, Filter (α i)) : Filter (∀ i, α i) :=
  ⨆ i : ι, comap (eval i) (f i)
/-
**Filter.mem_coprod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_coprodᵢ_iff {s : Set (∀ i, α i)} :
    s ∈ Filter.coprodᵢ f ↔ ∀ i : ι, ∃ t₁ ∈ f i, eval i ⁻¹' t₁ ⊆ s := by simp [Filter.coprodᵢ]
/-
**Filter.compl_mem_coprod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：compl_mem_coprod {s : Set (α × β)} {la : Filter α} {lb : Filter β} : sᶜ in
 la.coprod lb ↔ (Prod.fst '' s)ᶜ in la ∧ (Prod.snd '' s)ᶜ in lb
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem compl_mem_coprodᵢ {s : Set (∀ i, α i)} :
    sᶜ ∈ Filter.coprodᵢ f ↔ ∀ i, (eval i '' s)ᶜ ∈ f i := by
  simp only [Filter.coprodᵢ, mem_iSup, compl_mem_comap]
/-
**Filter.coprod** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Filter α → Filter β → Filter (α × β)
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprodᵢ_neBot_iff' :
    NeBot (Filter.coprodᵢ f) ↔ (∀ i, Nonempty (α i)) ∧ ∃ d, NeBot (f d) := by
  simp only [Filter.coprodᵢ, iSup_neBot, ← exists_and_left, ← comap_eval_neBot_iff']

@[simp]
/-
**Filter.coprod** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Filter α → Filter β → Filter (α × β)
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprodᵢ_neBot_iff [∀ i, Nonempty (α i)] : NeBot (Filter.coprodᵢ f) ↔ ∃ d, NeBot (f d) := by
  simp [coprodᵢ_neBot_iff', *]
/-
**Filter.coprod** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Filter α → Filter β → Filter (α × β)
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprodᵢ_eq_bot_iff' : Filter.coprodᵢ f = ⊥ ↔ (∃ i, IsEmpty (α i)) ∨ f = ⊥ := by
  simpa only [not_neBot, not_and_or, funext_iff, not_forall, not_exists, not_nonempty_iff]
    using! coprodᵢ_neBot_iff'.not

@[simp]
/-
**Filter.coprod** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Filter α → Filter β → Filter (α × β)
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprodᵢ_eq_bot_iff [∀ i, Nonempty (α i)] : Filter.coprodᵢ f = ⊥ ↔ f = ⊥ := by
  simpa [funext_iff] using coprodᵢ_neBot_iff.not
/-
**Filter.coprod** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Filter α → Filter β → Filter (α × β)
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coprodᵢ_bot' : Filter.coprodᵢ (⊥ : ∀ i, Filter (α i)) = ⊥ :=
  coprodᵢ_eq_bot_iff'.2 (Or.inr rfl)

@[simp]
/-
**Filter.coprod** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Filter α → Filter β → Filter (α × β)
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprodᵢ_bot : Filter.coprodᵢ (fun _ => ⊥ : ∀ i, Filter (α i)) = ⊥ :=
  coprodᵢ_bot'
/-
**Filter.NeBot.coprod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem NeBot.coprodᵢ [∀ i, Nonempty (α i)] {i : ι} (h : NeBot (f i)) : NeBot (Filter.coprodᵢ f) :=
  coprodᵢ_neBot_iff.2 ⟨i, h⟩

@[instance]
/-
**Filter.coprod** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Filter α → Filter β → Filter (α × β)
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprodᵢ_neBot [∀ i, Nonempty (α i)] [Nonempty ι] (f : ∀ i, Filter (α i))
    [H : ∀ i, NeBot (f i)] : NeBot (Filter.coprodᵢ f) :=
  (H (Classical.arbitrary ι)).coprodᵢ

@[gcongr, mono]
/-
**Filter.coprod** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Filter α → Filter β → Filter (α × β)
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprodᵢ_mono (hf : ∀ i, f₁ i ≤ f₂ i) : Filter.coprodᵢ f₁ ≤ Filter.coprodᵢ f₂ :=
  iSup_mono fun i => comap_mono (hf i)

variable {β : ι → Type*} {m : ∀ i, α i → β i}
/-
**Filter.map_pi_map_coprod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_pi_map_coprodᵢ_le :
    map (fun k : ∀ i, α i => fun i => m i (k i)) (Filter.coprodᵢ f) ≤
      Filter.coprodᵢ fun i => map (m i) (f i) := by
  simp only [le_def, mem_map, mem_coprodᵢ_iff]
  intro s h i
  obtain ⟨t, H, hH⟩ := h i
  exact ⟨{ x : α i | m i x ∈ t }, H, fun x hx => hH hx⟩
/-
**Filter.Tendsto.pi_map_coprod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tendsto.pi_map_coprodᵢ {g : ∀ i, Filter (β i)} (h : ∀ i, Tendsto (m i) (f i) (g i)) :
    Tendsto (fun k : ∀ i, α i => fun i => m i (k i)) (Filter.coprodᵢ f) (Filter.coprodᵢ g) :=
  map_pi_map_coprodᵢ_le.trans (coprodᵢ_mono h)

end CoprodCat

end Filter

