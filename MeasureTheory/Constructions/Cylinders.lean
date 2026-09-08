/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber, Yaël Dillies, Kin Yau James Wong
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.Topology.Constructions

/-!
# π-systems of cylinders and square cylinders

The instance `MeasurableSpace.pi` on `∀ i, α i`, where each `α i` has a `MeasurableSpace` `m i`,
is defined as `⨆ i, (m i).comap (fun a => a i)`.
That is, a function `g : β → ∀ i, α i` is measurable iff for all `i`, the function `b ↦ g b i`
is measurable.

We define two π-systems generating `MeasurableSpace.pi`, cylinders and square cylinders.

## Main definitions

Given a finite set `s` of indices, a cylinder is the product of a set of `∀ i : s, α i` and of
`univ` on the other indices. A square cylinder is a cylinder for which the set on `∀ i : s, α i` is
a product set.

* `cylinder s S`: cylinder with base set `S : Set (∀ i : s, α i)` where `s` is a `Finset`
* `squareCylinders C` with `C : ∀ i, Set (Set (α i))`: set of all square cylinders such that for
  all `i` in the finset defining the box, the projection to `α i` belongs to `C i`. The main
  application of this is with `C i = {s : Set (α i) | MeasurableSet s}`.
* `measurableCylinders`: set of all cylinders with measurable base sets.
* `cylinderEvents Δ`: The σ-algebra of cylinder events on `Δ`. It is the smallest σ-algebra making
  the projections on the `i`-th coordinate continuous for all `i ∈ Δ`.

## Main statements

* `generateFrom_squareCylinders`: square cylinders formed from measurable sets generate the product
  σ-algebra
* `generateFrom_measurableCylinders`: cylinders formed from measurable sets generate the
  product σ-algebra

-/

@[expose] public section

open Function Set MeasurableSpace

namespace MeasureTheory

variable {ι : Type _} {α : ι → Type _}

section squareCylinders

/-- Given a finite set `s` of indices, a square cylinder is the product of a set `S` of
`∀ i : s, α i` and of `univ` on the other indices. The set `S` is a product of sets `t i` such that
for all `i : s`, `t i ∈ C i`.
`squareCylinders` is the set of all such square cylinders. -/
/-
**MeasureTheory.squareCylinders** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：squareCylinders (C : forall i, Set (Set (α i))) : Set (Set (forall i, α i)
)
参数：C : forall i, Set (Set (α i))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finite set `s` of indices, a square cylinder is the product of a set `S`
 of
`∀ i : s, α i` and of `univ` on the other indices. The set `S` is a product of s
ets `t i` such that
for all `i : s`, `t i ∈ C i`.
`squareCylinders` is the set of all such square cylinders.
-/
def squareCylinders (C : ∀ i, Set (Set (α i))) : Set (Set (∀ i, α i)) :=
  {S | ∃ s : Finset ι, ∃ t ∈ univ.pi C, S = (s : Set ι).pi t}
/-
**MeasureTheory.squareCylinders_eq_iUnion_image** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：squareCylinders_eq_iUnion_image (C : forall i, Set (Set (α i))) : squareCy
linders C = ⋃ s : Finset ι, (fun t => (s : Set ι).pi t) '' univ.pi C
参数：C : forall i, Set (Set (α i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem squareCylinders_eq_iUnion_image (C : ∀ i, Set (Set (α i))) :
    squareCylinders C = ⋃ s : Finset ι, (fun t ↦ (s : Set ι).pi t) '' univ.pi C := by
  ext1 f
  simp only [squareCylinders, mem_iUnion, mem_image, mem_univ_pi, mem_ofPred_eq,
    eq_comm (a := f)]
/-
**MeasureTheory.isPiSystem_squareCylinders** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：isPiSystem_squareCylinders {C : forall i, Set (Set (α i))} (hC : forall i,
 IsPiSystem (C i)) (hC_univ : forall i, univ in C i) : IsPiSystem (squareCylinde
rs C)
参数：Set (α i)；hC : forall i, IsPiSystem (C i)；hC_univ : forall i, univ in C i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : ι} (hi : i in s) : 
s.piecewise f g i = f i
· 使用引理 `Finset.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : ι} (hi : i ∉ 
s) : s.piecewise f g i = g i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pi_congr`：pi_congr (h : s₁ = s₂) (h' : forall i in s₁, t₁ i = t₂ i) 
: s₁.pi t₁ = s₂.pi t₂
· 使用定理 `Set.union_pi_inter`：union_pi_inter (ht₁ : forall i ∉ s₁, t₁ i = univ) (h
t₂ : forall i ∉ s₂, t₂ i = univ) : (s₁ union s₂).pi (fun i => t₁ i inter t₂ i) =
 s₁.pi t…
· 使用定理 `Set.mem_univ_pi`：mem_univ_pi : f in pi univ t ↔ forall i, f i in t i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_pi`：∀ {ι : Type u_1} {α : ι → Type u_2} {s : Set ι} {t : (i : ι)
 → Set (α i)} {f : (i : ι) → α i},   f ∈ s.pi t ↔ ∀ i ∈ s, f i ∈ t i
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
-/
theorem isPiSystem_squareCylinders {C : ∀ i, Set (Set (α i))} (hC : ∀ i, IsPiSystem (C i))
    (hC_univ : ∀ i, univ ∈ C i) :
    IsPiSystem (squareCylinders C) := by
  rintro S₁ ⟨s₁, t₁, h₁, rfl⟩ S₂ ⟨s₂, t₂, h₂, rfl⟩ hst_nonempty
  classical
  let t₁' := s₁.piecewise t₁ (fun i ↦ univ)
  let t₂' := s₂.piecewise t₂ (fun i ↦ univ)
  have h1 : ∀ i ∈ (s₁ : Set ι), t₁ i = t₁' i :=
    fun i hi ↦ (Finset.piecewise_eq_of_mem _ _ _ hi).symm
  have h1' : ∀ i ∉ (s₁ : Set ι), t₁' i = univ :=
    fun i hi ↦ Finset.piecewise_eq_of_notMem _ _ _ hi
  have h2 : ∀ i ∈ (s₂ : Set ι), t₂ i = t₂' i :=
    fun i hi ↦ (Finset.piecewise_eq_of_mem _ _ _ hi).symm
  have h2' : ∀ i ∉ (s₂ : Set ι), t₂' i = univ :=
    fun i hi ↦ Finset.piecewise_eq_of_notMem _ _ _ hi
  rw [Set.pi_congr rfl h1, Set.pi_congr rfl h2, ← union_pi_inter h1' h2']
  refine ⟨s₁ ∪ s₂, fun i ↦ t₁' i ∩ t₂' i, ?_, ?_⟩
  · rw [mem_univ_pi]
    intro i
    have : (t₁' i ∩ t₂' i).Nonempty := by
      obtain ⟨f, hf⟩ := hst_nonempty
      rw [Set.pi_congr rfl h1, Set.pi_congr rfl h2, mem_inter_iff, mem_pi, mem_pi] at hf
      refine ⟨f i, ⟨?_, ?_⟩⟩
      · by_cases hi₁ : i ∈ s₁
        · exact hf.1 i hi₁
        · rw [h1' i hi₁]
          exact mem_univ _
      · by_cases hi₂ : i ∈ s₂
        · exact hf.2 i hi₂
        · rw [h2' i hi₂]
          exact mem_univ _
    refine hC i _ ?_ _ ?_ this
    · by_cases hi₁ : i ∈ s₁
      · rw [← h1 i hi₁]
        exact h₁ i (mem_univ _)
      · rw [h1' i hi₁]
        exact hC_univ i
    · by_cases hi₂ : i ∈ s₂
      · rw [← h2 i hi₂]
        exact h₂ i (mem_univ _)
      · rw [h2' i hi₂]
        exact hC_univ i
  · rw [Finset.coe_union]
/-
**MeasureTheory.comap_eval_le_generateFrom_squareCylinders_singleton** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：comap_eval_le_generateFrom_squareCylinders_singleton (α : ι -> Type*) [m :
 forall i, MeasurableSpace (α i)] (i : ι) : MeasurableSpace.comap (Function.eval
 i) (m i) <= MeasurableSpace.generateFrom ((fun t => ({i} : Set ι).pi t) '' univ
.pi fun i => {s : Set (α i) | MeasurableSet s})
参数：α : ι -> Type*；α i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.singleton_pi`：singleton_pi (i : ι) (t : forall i, Set (α i)) : pi {i
} t = eval i ⁻¹' t i
· 使用定理 `MeasurableSpace.comap_eq_generateFrom`：comap_eq_generateFrom (m : Measur
ableSpace β) (f : α -> β) : m.comap f = generateFrom { t | exists s, MeasurableS
et s ∧ f ⁻¹' s = t }
· 使用定理 `MeasurableSpace.generateFrom_mono`：generateFrom_mono {s t : Set (Set α)}
 (h : s subseteq t) : generateFrom s <= generateFrom t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
-/
theorem comap_eval_le_generateFrom_squareCylinders_singleton
    (α : ι → Type*) [m : ∀ i, MeasurableSpace (α i)] (i : ι) :
    MeasurableSpace.comap (Function.eval i) (m i) ≤
      MeasurableSpace.generateFrom
        ((fun t ↦ ({i} : Set ι).pi t) '' univ.pi fun i ↦ {s : Set (α i) | MeasurableSet s}) := by
  simp only [singleton_pi]
  rw [MeasurableSpace.comap_eq_generateFrom]
  refine MeasurableSpace.generateFrom_mono fun S ↦ ?_
  simp only [mem_ofPred_eq, mem_image, mem_univ_pi, forall_exists_index, and_imp]
  intro t ht h
  classical
  refine ⟨fun j ↦ if hji : j = i then by convert! t else univ, fun j ↦ ?_, ?_⟩
  · by_cases hji : j = i
    · simp only [hji, eq_mpr_eq_cast, dif_pos]
      convert! ht
      simp only [cast_heq]
    · simp only [hji, not_false_iff, dif_neg, MeasurableSet.univ]
  · #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was: `grind` -/
    simp [h]

/-- The square cylinders formed from measurable sets generate the product σ-algebra. -/
/-
**MeasureTheory.generateFrom_squareCylinders** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：generateFrom_squareCylinders [forall i, MeasurableSpace (α i)] : Measurabl
eSpace.generateFrom (squareCylinders fun i => {s : Set (α i) | MeasurableSet s})
 = MeasurableSpace.pi
参数：α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSpace.generateFrom_le_iff`：generateFrom_le_iff {s : Set (Set α
)} (m : MeasurableSpace α) : generateFrom s <= m ↔ s subseteq { t | MeasurableSe
t[m] t }
· 使用定理 `MeasurableSet.pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : δ) → 
MeasurableSpace (X a)] {s : Set δ} {t : (i : δ) → Set (X i)},   s.Countable → (∀
 i ∈ s…
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.comap_eval_le_generateFrom_squareCylinders_singleton`：coma
p_eval_le_generateFrom_squareCylinders_singleton (α : ι -> Type*) [m : forall i,
 MeasurableSpace (α i)] (i : ι) : MeasurableSpace.comap …
· 使用定理 `MeasurableSpace.generateFrom_mono`：generateFrom_mono {s t : Set (Set α)}
 (h : s subseteq t) : generateFrom s <= generateFrom t
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `MeasureTheory.squareCylinders_eq_iUnion_image`：squareCylinders_eq_iUnion
_image (C : forall i, Set (Set (α i))) : squareCylinders C = ⋃ s : Finset ι, (fu
n t => (s : Set ι).pi t) '' univ.pi…
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i

--- 原说明 ---
The square cylinders formed from measurable sets generate the product σ-algebra.
-/
theorem generateFrom_squareCylinders [∀ i, MeasurableSpace (α i)] :
    MeasurableSpace.generateFrom (squareCylinders fun i ↦ {s : Set (α i) | MeasurableSet s}) =
      MeasurableSpace.pi := by
  apply le_antisymm
  · rw [MeasurableSpace.generateFrom_le_iff]
    rintro S ⟨s, t, h, rfl⟩
    simp only [mem_univ_pi, mem_ofPred_eq] at h
    exact MeasurableSet.pi (Finset.countable_toSet _) (fun i _ ↦ h i)
  · refine iSup_le fun i ↦ ?_
    refine (comap_eval_le_generateFrom_squareCylinders_singleton α i).trans ?_
    refine MeasurableSpace.generateFrom_mono ?_
    rw [← Finset.coe_singleton, squareCylinders_eq_iUnion_image]
    exact subset_iUnion
      (fun (s : Finset ι) ↦
        (fun t : ∀ i, Set (α i) ↦ (s : Set ι).pi t) '' univ.pi (fun i ↦ Set.ofPred MeasurableSet))
      ({i} : Finset ι)

end squareCylinders

section cylinder

/-- Given a finite set `s` of indices, a cylinder is the preimage of a set `S` of `∀ i : s, α i` by
the projection from `∀ i, α i` to `∀ i : s, α i`. -/
/-
**MeasureTheory.cylinder** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：cylinder (s : Finset ι) (S : Set (forall i : s, α i)) : Set (forall i, α i
)
参数：s : Finset ι；S : Set (forall i : s, α i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finite set `s` of indices, a cylinder is the preimage of a set `S` of `∀
 i : s, α i` by
the projection from `∀ i, α i` to `∀ i : s, α i`.
-/
def cylinder (s : Finset ι) (S : Set (∀ i : s, α i)) : Set (∀ i, α i) :=
  s.restrict ⁻¹' S

@[simp]
/-
**MeasureTheory.mem_cylinder** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：mem_cylinder (s : Finset ι) (S : Set (forall i : s, α i)) (f : forall i, α
 i) : f in cylinder s S ↔ s.restrict f in S
参数：s : Finset ι；S : Set (forall i : s, α i)；f : forall i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
-/
theorem mem_cylinder (s : Finset ι) (S : Set (∀ i : s, α i)) (f : ∀ i, α i) :
    f ∈ cylinder s S ↔ s.restrict f ∈ S :=
  mem_preimage

@[simp]
/-
**MeasureTheory.cylinder_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：cylinder_empty (s : Finset ι) : cylinder s (∅ : Set (forall i : s, α i)) =
 ∅
参数：s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.cylinder.eq_1`：∀ {ι : Type u_1} {α : ι → Type u_2} (s : Fi
nset ι) (S : Set ((i : ↥s) → α ↑i)),   MeasureTheory.cylinder s S = s.restrict ⁻
¹' S
· 使用定理 `Set.preimage_empty`：preimage_empty : f ⁻¹' ∅ = ∅
-/
theorem cylinder_empty (s : Finset ι) : cylinder s (∅ : Set (∀ i : s, α i)) = ∅ := by
  rw [cylinder, preimage_empty]

@[simp]
/-
**MeasureTheory.cylinder_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：cylinder_univ (s : Finset ι) : cylinder s (univ : Set (forall i : s, α i))
 = univ
参数：s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.cylinder.eq_1`：∀ {ι : Type u_1} {α : ι → Type u_2} (s : Fi
nset ι) (S : Set ((i : ↥s) → α ↑i)),   MeasureTheory.cylinder s S = s.restrict ⁻
¹' S
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
-/
theorem cylinder_univ (s : Finset ι) : cylinder s (univ : Set (∀ i : s, α i)) = univ := by
  rw [cylinder, preimage_univ]

@[simp]
/-
**MeasureTheory.cylinder_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：cylinder_eq_empty_iff [h_nonempty : Nonempty (forall i, α i)] (s : Finset 
ι) (S : Set (forall i : s, α i)) : cylinder s S = ∅ ↔ S = ∅
参数：forall i, α i；s : Finset ι；S : Set (forall i : s, α i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `MeasureTheory.mem_cylinder`：mem_cylinder (s : Finset ι) (S : Set (forall
 i : s, α i)) (f : forall i, α i) : f in cylinder s S ↔ s.restrict f in S
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
· 使用定理 `MeasureTheory.cylinder_empty`：cylinder_empty (s : Finset ι) : cylinder s
 (∅ : Set (forall i : s, α i)) = ∅
-/
theorem cylinder_eq_empty_iff [h_nonempty : Nonempty (∀ i, α i)] (s : Finset ι)
    (S : Set (∀ i : s, α i)) :
    cylinder s S = ∅ ↔ S = ∅ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by (rw [h]; exact cylinder_empty _)⟩
  by_contra hS
  rw [← Ne, ← nonempty_iff_ne_empty] at hS
  let f := hS.some
  have hf : f ∈ S := hS.choose_spec
  classical
  let f' : ∀ i, α i := fun i ↦ if hi : i ∈ s then f ⟨i, hi⟩ else h_nonempty.some i
  have hf' : f' ∈ cylinder s S := by
    rw [mem_cylinder]
    simpa only [Finset.restrict_def, Finset.coe_mem, dif_pos, f']
  rw [h] at hf'
  exact notMem_empty _ hf'
/-
**MeasureTheory.inter_cylinder** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：inter_cylinder (s₁ s₂ : Finset ι) (S₁ : Set (forall i : s₁, α i)) (S₂ : Se
t (forall i : s₂, α i)) [DecidableEq ι] : cylinder s₁ S₁ inter cylinder s₂ S₂ = 
cylinder (s₁ union s₂) (Finset.restrict₂ Finset.subset_union_left ⁻¹' S₁ inter F
inset.restrict₂ Finset.subset_union_right ⁻¹' S₂)
参数：s₁ s₂ : Finset ι；S₁ : Set (forall i : s₁, α i)；S₂ : Set (forall i : s₂, α i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_cylinder (s₁ s₂ : Finset ι) (S₁ : Set (∀ i : s₁, α i)) (S₂ : Set (∀ i : s₂, α i))
    [DecidableEq ι] :
    cylinder s₁ S₁ ∩ cylinder s₂ S₂ =
      cylinder (s₁ ∪ s₂)
        (Finset.restrict₂ Finset.subset_union_left ⁻¹' S₁ ∩
          Finset.restrict₂ Finset.subset_union_right ⁻¹' S₂) := rfl
/-
**MeasureTheory.inter_cylinder_same** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：inter_cylinder_same (s : Finset ι) (S₁ : Set (forall i : s, α i)) (S₂ : Se
t (forall i : s, α i)) : cylinder s S₁ inter cylinder s S₂ = cylinder s (S₁ inte
r S₂)
参数：s : Finset ι；S₁ : Set (forall i : s, α i)；S₂ : Set (forall i : s, α i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_cylinder_same (s : Finset ι) (S₁ : Set (∀ i : s, α i)) (S₂ : Set (∀ i : s, α i)) :
    cylinder s S₁ ∩ cylinder s S₂ = cylinder s (S₁ ∩ S₂) := rfl
/-
**MeasureTheory.union_cylinder** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：union_cylinder (s₁ s₂ : Finset ι) (S₁ : Set (forall i : s₁, α i)) (S₂ : Se
t (forall i : s₂, α i)) [DecidableEq ι] : cylinder s₁ S₁ union cylinder s₂ S₂ = 
cylinder (s₁ union s₂) (Finset.restrict₂ Finset.subset_union_left ⁻¹' S₁ union F
inset.restrict₂ Finset.subset_union_right ⁻¹' S₂)
参数：s₁ s₂ : Finset ι；S₁ : Set (forall i : s₁, α i)；S₂ : Set (forall i : s₂, α i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem union_cylinder (s₁ s₂ : Finset ι) (S₁ : Set (∀ i : s₁, α i)) (S₂ : Set (∀ i : s₂, α i))
    [DecidableEq ι] :
    cylinder s₁ S₁ ∪ cylinder s₂ S₂ =
      cylinder (s₁ ∪ s₂)
        (Finset.restrict₂ Finset.subset_union_left ⁻¹' S₁ ∪
          Finset.restrict₂ Finset.subset_union_right ⁻¹' S₂) := rfl
/-
**MeasureTheory.union_cylinder_same** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：union_cylinder_same (s : Finset ι) (S₁ : Set (forall i : s, α i)) (S₂ : Se
t (forall i : s, α i)) : cylinder s S₁ union cylinder s S₂ = cylinder s (S₁ unio
n S₂)
参数：s : Finset ι；S₁ : Set (forall i : s, α i)；S₂ : Set (forall i : s, α i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem union_cylinder_same (s : Finset ι) (S₁ : Set (∀ i : s, α i)) (S₂ : Set (∀ i : s, α i)) :
    cylinder s S₁ ∪ cylinder s S₂ = cylinder s (S₁ ∪ S₂) := rfl
/-
**MeasureTheory.compl_cylinder** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：compl_cylinder (s : Finset ι) (S : Set (forall i : s, α i)) : (cylinder s 
S)ᶜ = cylinder s (Sᶜ)
参数：s : Finset ι；S : Set (forall i : s, α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem compl_cylinder (s : Finset ι) (S : Set (∀ i : s, α i)) :
    (cylinder s S)ᶜ = cylinder s (Sᶜ) := by
  ext1 f; simp only [mem_compl_iff, mem_cylinder]
/-
**MeasureTheory.sdiff_cylinder_same** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：sdiff_cylinder_same (s : Finset ι) (S T : Set (forall i : s, α i)) : cylin
der s S \ cylinder s T = cylinder s (S \ T)
参数：s : Finset ι；S T : Set (forall i : s, α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sdiff_cylinder_same (s : Finset ι) (S T : Set (∀ i : s, α i)) :
    cylinder s S \ cylinder s T = cylinder s (S \ T) := by
  ext1 f; simp only [mem_sdiff, mem_cylinder]

@[deprecated (since := "2026-06-03")] alias diff_cylinder_same := sdiff_cylinder_same
/-
**MeasureTheory.eq_of_cylinder_eq_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：eq_of_cylinder_eq_of_subset [h_nonempty : Nonempty (forall i, α i)] {I J :
 Finset ι} {S : Set (forall i : I, α i)} {T : Set (forall i : J, α i)} (h_eq : c
ylinder I S = cylinder J T) (hJI : J subseteq I) : S = Finset.restrict₂ hJI ⁻¹' 
T
参数：forall i, α i；forall i : I, α i；forall i : J, α i；h_eq : cylinder I S = cylin
der J T；hJI : J subseteq I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
-/
theorem eq_of_cylinder_eq_of_subset [h_nonempty : Nonempty (∀ i, α i)] {I J : Finset ι}
    {S : Set (∀ i : I, α i)} {T : Set (∀ i : J, α i)} (h_eq : cylinder I S = cylinder J T)
    (hJI : J ⊆ I) :
    S = Finset.restrict₂ hJI ⁻¹' T := by
  rw [Set.ext_iff] at h_eq
  simp only [mem_cylinder] at h_eq
  ext1 f
  simp only [mem_preimage]
  classical
  specialize h_eq fun i ↦ if hi : i ∈ I then f ⟨i, hi⟩ else h_nonempty.some i
  have h_mem : ∀ j : J, ↑j ∈ I := fun j ↦ hJI j.prop
  simpa only [Finset.restrict_def, Finset.coe_mem, dite_true, h_mem] using! h_eq
/-
**MeasureTheory.cylinder_eq_cylinder_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：cylinder_eq_cylinder_union [DecidableEq ι] (I : Finset ι) (S : Set (forall
 i : I, α i)) (J : Finset ι) : cylinder I S = cylinder (I union J) (Finset.restr
ict₂ Finset.subset_union_left ⁻¹' S)
参数：I : Finset ι；S : Set (forall i : I, α i)；J : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cylinder_eq_cylinder_union [DecidableEq ι] (I : Finset ι) (S : Set (∀ i : I, α i))
    (J : Finset ι) :
    cylinder I S =
      cylinder (I ∪ J) (Finset.restrict₂ Finset.subset_union_left ⁻¹' S) := by
  ext1 f; simp only [mem_cylinder, Finset.restrict_def, Finset.restrict₂_def, mem_preimage]
/-
**MeasureTheory.disjoint_cylinder_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：disjoint_cylinder_iff [Nonempty (forall i, α i)] {s t : Finset ι} {S : Set
 (forall i : s, α i)} {T : Set (forall i : t, α i)} [DecidableEq ι] : Disjoint (
cylinder s S) (cylinder t T) ↔ Disjoint (Finset.restrict₂ Finset.subset_union_le
ft ⁻¹' S) (Finset.restrict₂ Finset.subset_union_right ⁻¹' T)
参数：forall i, α i；forall i : s, α i；forall i : t, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_cylinder_iff [Nonempty (∀ i, α i)] {s t : Finset ι} {S : Set (∀ i : s, α i)}
    {T : Set (∀ i : t, α i)} [DecidableEq ι] :
    Disjoint (cylinder s S) (cylinder t T) ↔
      Disjoint
        (Finset.restrict₂ Finset.subset_union_left ⁻¹' S)
        (Finset.restrict₂ Finset.subset_union_right ⁻¹' T) := by
  simp_rw [Set.disjoint_iff, subset_empty_iff, inter_cylinder, cylinder_eq_empty_iff]
/-
**MeasureTheory.IsClosed.cylinder** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.IsClo
sed`。
形式化陈述：∀ {ι : Type u_2} {α : ι → Type u_1} [inst : (i : ι) → TopologicalSpace (α 
i)] (s : Finset ι)   {S : Set ((i : ↥s) → α ↑i)}, IsClosed S → IsClosed (Measure
Theory.cylinder s S)
参数：i : ι；α i；s : Finset ι；(i : ↥s) → α ↑i；MeasureTheory.cylinder s S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem IsClosed.cylinder [∀ i, TopologicalSpace (α i)] (s : Finset ι) {S : Set (∀ i : s, α i)}
    (hs : IsClosed S) : IsClosed (cylinder s S) :=
  hs.preimage (continuous_pi fun _ ↦ continuous_apply _)
/-
**MeasureTheory._root_.MeasurableSet.cylinder** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableSet.cylinder [∀ i, MeasurableSpace (α i)] (s : Finset ι)
    {S : Set (∀ i : s, α i)} (hS : MeasurableSet S) :
    MeasurableSet (cylinder s S) :=
  measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _) hS

/-- The indicator of a cylinder only depends on the variables whose the cylinder depends on. -/
/-
**MeasureTheory.dependsOn_cylinder_indicator_const** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：dependsOn_cylinder_indicator_const {M : Type*} [Zero M] {I : Finset ι} (S 
: Set (Π i : I, α i)) (c : M) : DependsOn ((cylinder I S).indicator (fun _ => c)
) I
参数：S : Set (Π i : I, α i)；c : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.indicator_const_eq_indicator_const`：∀ {α : Type u_1} {β : Type u_2} 
{M : Type u_3} [inst : Zero M] {s : Set α} {a : α} {t : Set β} {b : β} {c : M}, 
  (a ∈ s ↔ b ∈ t) → s.indica…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The indicator of a cylinder only depends on the variables whose the cylinder dep
ends on.
-/
theorem dependsOn_cylinder_indicator_const {M : Type*} [Zero M] {I : Finset ι}
    (S : Set (Π i : I, α i)) (c : M) :
    DependsOn ((cylinder I S).indicator (fun _ ↦ c)) I :=
  fun x y hxy ↦ Set.indicator_const_eq_indicator_const (by simp [Finset.restrict_def, hxy])

end cylinder

section cylinders

/-- Given a finite set `s` of indices, a cylinder is the preimage of a set `S` of `∀ i : s, α i` by
the projection from `∀ i, α i` to `∀ i : s, α i`.
`measurableCylinders` is the set of all cylinders with measurable base `S`. -/
/-
**MeasureTheory.measurableCylinders** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：measurableCylinders (α : ι -> Type*) [forall i, MeasurableSpace (α i)] : S
et (Set (forall i, α i))
参数：α : ι -> Type*；α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finite set `s` of indices, a cylinder is the preimage of a set `S` of `∀
 i : s, α i` by
the projection from `∀ i, α i` to `∀ i : s, α i`.
`measurableCylinders` is the set of all cylinders with measurable base `S`.
-/
def measurableCylinders (α : ι → Type*) [∀ i, MeasurableSpace (α i)] : Set (Set (∀ i, α i)) :=
  ⋃ (s) (S) (_ : MeasurableSet S), {cylinder s S}
/-
**MeasureTheory.empty_mem_measurableCylinders** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：empty_mem_measurableCylinders (α : ι -> Type*) [forall i, MeasurableSpace 
(α i)] : ∅ in measurableCylinders α
参数：α : ι -> Type*；α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.cylinder_empty`：cylinder_empty (s : Finset ι) : cylinder s
 (∅ : Set (forall i : s, α i)) = ∅
-/
theorem empty_mem_measurableCylinders (α : ι → Type*) [∀ i, MeasurableSpace (α i)] :
    ∅ ∈ measurableCylinders α := by
  simp_rw [measurableCylinders, mem_iUnion, mem_singleton_iff]
  exact ⟨∅, ∅, MeasurableSet.empty, (cylinder_empty _).symm⟩

variable [∀ i, MeasurableSpace (α i)] {s t : Set (∀ i, α i)}

@[simp]
/-
**MeasureTheory.mem_measurableCylinders** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：mem_measurableCylinders (t : Set (forall i, α i)) : t in measurableCylinde
rs α ↔ exists s S, MeasurableSet S ∧ t = cylinder s S
参数：t : Set (forall i, α i)。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_measurableCylinders (t : Set (∀ i, α i)) :
    t ∈ measurableCylinders α ↔ ∃ s S, MeasurableSet S ∧ t = cylinder s S := by
  simp_rw [measurableCylinders, mem_iUnion, exists_prop, mem_singleton_iff]

@[measurability]
/-
**MeasureTheory._root_.MeasurableSet.of_mem_measurableCylinders** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableSet.of_mem_measurableCylinders {s : Set (Π i, α i)}
    (hs : s ∈ measurableCylinders α) : MeasurableSet s := by
  obtain ⟨I, t, mt, rfl⟩ := (mem_measurableCylinders s).1 hs
  exact mt.cylinder

/-- A finset `s` such that `t = cylinder s S`. `S` is given by `measurableCylinders.set`. -/
/-
**MeasureTheory.measurableCylinders.finset** 是 Mathlib 中的一个定义，位于命名空间 `MeasureThe
ory.measurableCylinders`。
形式化陈述：{ι : Type u_1} →   {α : ι → Type u_2} →     [inst : (i : ι) → MeasurableSp
ace (α i)] →       {t : Set ((i : ι) → α i)} → t ∈ MeasureTheory.measurableCylin
ders α → Finset ι
参数：i : ι；α i；(i : ι) → α i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finset `s` such that `t = cylinder s S`. `S` is given by `measurableCylinders.
set`.
-/
noncomputable def measurableCylinders.finset (ht : t ∈ measurableCylinders α) : Finset ι :=
  ((mem_measurableCylinders t).mp ht).choose

/-- A set `S` such that `t = cylinder s S`. `s` is given by `measurableCylinders.finset`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**MeasureTheory.measurableCylinders.set** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
.measurableCylinders`。
形式化陈述：{ι : Type u_1} →   {α : ι → Type u_2} →     [inst : (i : ι) → MeasurableSp
ace (α i)] →       {t : Set ((i : ι) → α i)} →         (ht : t ∈ MeasureTheory.m
easurableCylinders α) →           Set ((i : ↥(MeasureTheory.measurableCylinders.
finset ht)) → α ↑i)
参数：i : ι；α i；(i : ι) → α i；ht : t ∈ MeasureTheory.measurableCylinders α；(i : ↥(M
easureTheory.measurableCylinders.finset ht)) → α ↑i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def measurableCylinders.set (ht : t ∈ measurableCylinders α) :
    Set (∀ i : measurableCylinders.finset ht, α i) :=
  ((mem_measurableCylinders t).mp ht).choose_spec.choose
/-
**MeasureTheory.measurableCylinders.measurableSet** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.measurableCylinders`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → MeasurableSpace (α i
)] {t : Set ((i : ι) → α i)}   (ht : t ∈ MeasureTheory.measurableCylinders α), M
easurableSet (MeasureTheory.measurableCylinders.set ht)
参数：i : ι；α i；(i : ι) → α i；ht : t ∈ MeasureTheory.measurableCylinders α；MeasureT
heory.measurableCylinders.set ht。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.mem_measurableCylinders`：mem_measurableCylinders (t : Set 
(forall i, α i)) : t in measurableCylinders α ↔ exists s S, MeasurableSet S ∧ t 
= cylinder s S
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem measurableCylinders.measurableSet (ht : t ∈ measurableCylinders α) :
    MeasurableSet (measurableCylinders.set ht) :=
  ((mem_measurableCylinders t).mp ht).choose_spec.choose_spec.left
/-
**MeasureTheory.measurableCylinders.eq_cylinder** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.measurableCylinders`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → MeasurableSpace (α i
)] {t : Set ((i : ι) → α i)}   (ht : t ∈ MeasureTheory.measurableCylinders α),  
 t = MeasureTheory.cylinder (MeasureTheory.measurableCylinders.finset ht) (Measu
reTheory.measurableCylinders.set ht)
参数：i : ι；α i；(i : ι) → α i；ht : t ∈ MeasureTheory.measurableCylinders α；MeasureT
heory.measurableCylinders.finset ht；MeasureTheory.measurableCylinders.set ht。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.mem_measurableCylinders`：mem_measurableCylinders (t : Set 
(forall i, α i)) : t in measurableCylinders α ↔ exists s S, MeasurableSet S ∧ t 
= cylinder s S
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem measurableCylinders.eq_cylinder (ht : t ∈ measurableCylinders α) :
    t = cylinder (measurableCylinders.finset ht) (measurableCylinders.set ht) :=
  ((mem_measurableCylinders t).mp ht).choose_spec.choose_spec.right
/-
**MeasureTheory.cylinder_mem_measurableCylinders** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：cylinder_mem_measurableCylinders (s : Finset ι) (S : Set (forall i : s, α 
i)) (hS : MeasurableSet S) : cylinder s S in measurableCylinders α
参数：s : Finset ι；S : Set (forall i : s, α i)；hS : MeasurableSet S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.mem_measurableCylinders`：mem_measurableCylinders (t : Set 
(forall i, α i)) : t in measurableCylinders α ↔ exists s S, MeasurableSet S ∧ t 
= cylinder s S
-/
theorem cylinder_mem_measurableCylinders (s : Finset ι) (S : Set (∀ i : s, α i))
    (hS : MeasurableSet S) :
    cylinder s S ∈ measurableCylinders α := by
  rw [mem_measurableCylinders]; exact ⟨s, S, hS, rfl⟩
/-
**MeasureTheory.inter_mem_measurableCylinders** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：inter_mem_measurableCylinders (hs : s in measurableCylinders α) (ht : t in
 measurableCylinders α) : s inter t in measurableCylinders α
参数：hs : s in measurableCylinders α；ht : t in measurableCylinders α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.mem_measurableCylinders`：mem_measurableCylinders (t : Set 
(forall i, α i)) : t in measurableCylinders α ↔ exists s S, MeasurableSet S ∧ t 
= cylinder s S
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `MeasureTheory.inter_cylinder`：inter_cylinder (s₁ s₂ : Finset ι) (S₁ : Se
t (forall i : s₁, α i)) (S₂ : Set (forall i : s₂, α i)) [DecidableEq ι] : cylind
er s₁ S₁ inter cyl…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem inter_mem_measurableCylinders (hs : s ∈ measurableCylinders α)
    (ht : t ∈ measurableCylinders α) :
    s ∩ t ∈ measurableCylinders α := by
  rw [mem_measurableCylinders] at *
  obtain ⟨s₁, S₁, hS₁, rfl⟩ := hs
  obtain ⟨s₂, S₂, hS₂, rfl⟩ := ht
  classical
  refine ⟨s₁ ∪ s₂,
    Finset.restrict₂ Finset.subset_union_left ⁻¹' S₁ ∩
      {f | Finset.restrict₂ Finset.subset_union_right f ∈ S₂}, ?_, ?_⟩
  · refine MeasurableSet.inter ?_ ?_
    · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _) hS₁
    · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _) hS₂
  · exact inter_cylinder _ _ _ _
/-
**MeasureTheory.isPiSystem_measurableCylinders** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：isPiSystem_measurableCylinders : IsPiSystem (measurableCylinders α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.inter_mem_measurableCylinders`：inter_mem_measurableCylinde
rs (hs : s in measurableCylinders α) (ht : t in measurableCylinders α) : s inter
 t in measurableCylinders α
-/
theorem isPiSystem_measurableCylinders : IsPiSystem (measurableCylinders α) :=
  fun _ hS _ hT _ ↦ inter_mem_measurableCylinders hS hT
/-
**MeasureTheory.compl_mem_measurableCylinders** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：compl_mem_measurableCylinders (hs : s in measurableCylinders α) : sᶜ in me
asurableCylinders α
参数：hs : s in measurableCylinders α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.mem_measurableCylinders`：mem_measurableCylinders (t : Set 
(forall i, α i)) : t in measurableCylinders α ↔ exists s S, MeasurableSet S ∧ t 
= cylinder s S
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.compl_cylinder`：compl_cylinder (s : Finset ι) (S : Set (fo
rall i : s, α i)) : (cylinder s S)ᶜ = cylinder s (Sᶜ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem compl_mem_measurableCylinders (hs : s ∈ measurableCylinders α) :
    sᶜ ∈ measurableCylinders α := by
  rw [mem_measurableCylinders] at hs ⊢
  obtain ⟨s, S, hS, rfl⟩ := hs
  refine ⟨s, Sᶜ, hS.compl, ?_⟩
  rw [compl_cylinder]
/-
**MeasureTheory.univ_mem_measurableCylinders** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：univ_mem_measurableCylinders (α : ι -> Type*) [forall i, MeasurableSpace (
α i)] : Set.univ in measurableCylinders α
参数：α : ι -> Type*；α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `MeasureTheory.compl_mem_measurableCylinders`：compl_mem_measurableCylinde
rs (hs : s in measurableCylinders α) : sᶜ in measurableCylinders α
· 使用定理 `MeasureTheory.empty_mem_measurableCylinders`：empty_mem_measurableCylinde
rs (α : ι -> Type*) [forall i, MeasurableSpace (α i)] : ∅ in measurableCylinders
 α
-/
theorem univ_mem_measurableCylinders (α : ι → Type*) [∀ i, MeasurableSpace (α i)] :
    Set.univ ∈ measurableCylinders α := by
  rw [← compl_empty]; exact compl_mem_measurableCylinders (empty_mem_measurableCylinders α)
/-
**MeasureTheory.union_mem_measurableCylinders** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：union_mem_measurableCylinders (hs : s in measurableCylinders α) (ht : t in
 measurableCylinders α) : s union t in measurableCylinders α
参数：hs : s in measurableCylinders α；ht : t in measurableCylinders α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_compl_compl_inter_compl`：union_eq_compl_compl_inter_compl (
s t : Set α) : s union t = (sᶜ inter tᶜ)ᶜ
· 使用定理 `MeasureTheory.compl_mem_measurableCylinders`：compl_mem_measurableCylinde
rs (hs : s in measurableCylinders α) : sᶜ in measurableCylinders α
· 使用定理 `MeasureTheory.inter_mem_measurableCylinders`：inter_mem_measurableCylinde
rs (hs : s in measurableCylinders α) (ht : t in measurableCylinders α) : s inter
 t in measurableCylinders α
-/
theorem union_mem_measurableCylinders (hs : s ∈ measurableCylinders α)
    (ht : t ∈ measurableCylinders α) :
    s ∪ t ∈ measurableCylinders α := by
  rw [union_eq_compl_compl_inter_compl]
  exact compl_mem_measurableCylinders (inter_mem_measurableCylinders
    (compl_mem_measurableCylinders hs) (compl_mem_measurableCylinders ht))
/-
**MeasureTheory.sdiff_mem_measurableCylinders** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：sdiff_mem_measurableCylinders (hs : s in measurableCylinders α) (ht : t in
 measurableCylinders α) : s \ t in measurableCylinders α
参数：hs : s in measurableCylinders α；ht : t in measurableCylinders α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_eq_compl_inter`：sdiff_eq_compl_inter {s t : Set α} : s \ t = t
ᶜ inter s
· 使用定理 `MeasureTheory.inter_mem_measurableCylinders`：inter_mem_measurableCylinde
rs (hs : s in measurableCylinders α) (ht : t in measurableCylinders α) : s inter
 t in measurableCylinders α
· 使用定理 `MeasureTheory.compl_mem_measurableCylinders`：compl_mem_measurableCylinde
rs (hs : s in measurableCylinders α) : sᶜ in measurableCylinders α
-/
theorem sdiff_mem_measurableCylinders (hs : s ∈ measurableCylinders α)
    (ht : t ∈ measurableCylinders α) :
    s \ t ∈ measurableCylinders α := by
  rw [sdiff_eq_compl_inter]
  exact inter_mem_measurableCylinders (compl_mem_measurableCylinders ht) hs

@[deprecated (since := "2026-06-03")]
alias diff_mem_measurableCylinders := sdiff_mem_measurableCylinders

/-- The measurable cylinders generate the product σ-algebra. -/
/-
**MeasureTheory.generateFrom_measurableCylinders** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：generateFrom_measurableCylinders : MeasurableSpace.generateFrom (measurabl
eCylinders α) = MeasurableSpace.pi
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.mem_measurableCylinders`：mem_measurableCylinders (t : Set 
(forall i, α i)) : t in measurableCylinders α ↔ exists s S, MeasurableSet S ∧ t 
= cylinder s S
· 使用定理 `MeasurableSet.cylinder`：∀ {ι : Type u_2} {α : ι → Type u_1} [inst : (i :
 ι) → MeasurableSpace (α i)] (s : Finset ι) {S : Set ((i : ↥s) → α ↑i)},   Measu
rableSet S →…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.comap_eval_le_generateFrom_squareCylinders_singleton`：coma
p_eval_le_generateFrom_squareCylinders_singleton (α : ι -> Type*) [m : forall i,
 MeasurableSpace (α i)] (i : ι) : MeasurableSpace.comap …
· 使用定理 `MeasurableSpace.generateFrom_mono`：generateFrom_mono {s t : Set (Set α)}
 (h : s subseteq t) : generateFrom s <= generateFrom t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.singleton_pi`：singleton_pi (i : ι) (t : forall i, Set (α i)) : pi {i
} t = eval i ⁻¹' t i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The measurable cylinders generate the product σ-algebra.
-/
theorem generateFrom_measurableCylinders :
    MeasurableSpace.generateFrom (measurableCylinders α) = MeasurableSpace.pi := by
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le (fun S hS ↦ ?_)
    obtain ⟨s, S, hSm, rfl⟩ := (mem_measurableCylinders _).mp hS
    exact hSm.cylinder
  · refine iSup_le fun i ↦ ?_
    refine (comap_eval_le_generateFrom_squareCylinders_singleton α i).trans ?_
    refine MeasurableSpace.generateFrom_mono (fun x ↦ ?_)
    simp only [singleton_pi, mem_image, mem_pi, mem_univ, mem_ofPred_eq,
      forall_true_left, mem_measurableCylinders, forall_exists_index, and_imp]
    rintro t ht rfl
    refine ⟨{i}, {f | f ⟨i, Finset.mem_singleton_self i⟩ ∈ t i}, measurable_pi_apply _ (ht i), ?_⟩
    ext1 x
    simp only [mem_preimage, Function.eval, mem_cylinder, mem_ofPred_eq, Finset.restrict]

/-- The cylinders of a product space indexed by `ℕ` can be seen as depending on the first
coordinates. -/
/-
**MeasureTheory.measurableCylinders_nat** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measurableCylinders_nat {X : Nat -> Type*} [forall n, MeasurableSpace (X n
)] : measurableCylinders X = ⋃ (a) (S) (_ : MeasurableSet S), {cylinder (Finset.
Iic a) S}
参数：X n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finset.subset_Iic_sup_id`：subset_Iic_sup_id [OrderBot α] (s : Finset α) 
: s subseteq Iic (s.sup id)
· 使用定理 `Finset.measurable_restrict₂`：Finset.measurable_restrict₂ {s t : Finset δ
} (hst : s subseteq t) : Measurable (Finset.restrict₂ (π
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Finset.restrict₂_comp_restrict`：restrict₂_comp_restrict (hst : s subsete
q t) : (restrict₂ (π
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)

--- 原说明 ---
The cylinders of a product space indexed by `ℕ` can be seen as depending on the 
first
coordinates.
-/
theorem measurableCylinders_nat {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] :
    measurableCylinders X = ⋃ (a) (S) (_ : MeasurableSet S), {cylinder (Finset.Iic a) S} := by
  ext s
  simp only [mem_measurableCylinders, exists_prop, mem_iUnion]
  refine ⟨?_, fun ⟨N, S, mS, s_eq⟩ ↦ ⟨Finset.Iic N, S, mS, s_eq⟩⟩
  rintro ⟨t, S, mS, rfl⟩
  refine ⟨t.sup id, Finset.restrict₂ t.subset_Iic_sup_id ⁻¹' S,
    Finset.measurable_restrict₂ _ mS, ?_⟩
  unfold cylinder
  rw [← preimage_comp, Finset.restrict₂_comp_restrict]
  exact mem_singleton _

end cylinders

/-! ### Cylinder events as a sigma-algebra -/

section cylinderEvents

variable {α ι : Type*} {X : ι → Type*} {mα : MeasurableSpace α} [m : ∀ i, MeasurableSpace (X i)]
  {Δ Δ₁ Δ₂ : Set ι} {i : ι}

/-- The σ-algebra of cylinder events on `Δ`. It is the smallest σ-algebra making the projections
on the `i`-th coordinate measurable for all `i ∈ Δ`. -/
@[instance_reducible]
/-
**MeasureTheory.cylinderEvents** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：cylinderEvents (Δ : Set ι) : MeasurableSpace (forall i, X i)
参数：Δ : Set ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The σ-algebra of cylinder events on `Δ`. It is the smallest σ-algebra making the
 projections
on the `i`-th coordinate measurable for all `i ∈ Δ`.
-/
def cylinderEvents (Δ : Set ι) : MeasurableSpace (∀ i, X i) := ⨆ i ∈ Δ, (m i).comap fun σ ↦ σ i
/-
**MeasureTheory.cylinderEvents_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {ι : Type u_2} {X : ι → Type u_3} [m : (i : ι) → MeasurableSpace (X i)],
   MeasureTheory.cylinderEvents Set.univ = MeasurableSpace.pi
参数：i : ι；X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma cylinderEvents_univ : cylinderEvents (X := X) univ = MeasurableSpace.pi := by
  simp [cylinderEvents, MeasurableSpace.pi]

@[gcongr]
/-
**MeasureTheory.cylinderEvents_mono** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：cylinderEvents_mono (h : Δ₁ subseteq Δ₂) : cylinderEvents (X
参数：h : Δ₁ subseteq Δ₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_mono`：biSup_mono {p q : ι -> Prop} (hpq : forall i, p i -> q i) : 
⨆ (i) (_ : p i), f i <= ⨆ (i) (_ : q i), f i
-/
lemma cylinderEvents_mono (h : Δ₁ ⊆ Δ₂) : cylinderEvents (X := X) Δ₁ ≤ cylinderEvents Δ₂ :=
  biSup_mono h
/-
**MeasureTheory.cylinderEvents_le_pi** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：cylinderEvents_le_pi : cylinderEvents (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.cylinderEvents_univ`：∀ {ι : Type u_2} {X : ι → Type u_3} [
m : (i : ι) → MeasurableSpace (X i)],   MeasureTheory.cylinderEvents Set.univ = 
MeasurableSpace.pi
· 使用引理 `MeasureTheory.cylinderEvents_mono`：cylinderEvents_mono (h : Δ₁ subseteq 
Δ₂) : cylinderEvents (X
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
lemma cylinderEvents_le_pi : cylinderEvents (X := X) Δ ≤ MeasurableSpace.pi := by
  simpa using cylinderEvents_mono (subset_univ _)
/-
**MeasureTheory.measurable_cylinderEvents_iff** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：measurable_cylinderEvents_iff {g : α -> forall i, X i} : @Measurable _ _ _
 (cylinderEvents Δ) g ↔ forall ⦃i⦄, i in Δ -> Measurable fun a => g a i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasurableSpace.comap_iSup`：comap_iSup {m : ι -> MeasurableSpace α} : (⨆
 i, m i).comap g = ⨆ i, (m i).comap g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasurableSpace.comap_comp`：comap_comp {f : β -> α} {g : γ -> β} : (m.co
map f).comap g = m.comap (f ∘ g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma measurable_cylinderEvents_iff {g : α → ∀ i, X i} :
    @Measurable _ _ _ (cylinderEvents Δ) g ↔ ∀ ⦃i⦄, i ∈ Δ → Measurable fun a ↦ g a i := by
  simp_rw [measurable_iff_comap_le, cylinderEvents, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, iSup_le_iff]

@[fun_prop]
/-
**MeasureTheory.measurable_cylinderEvent_apply** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：measurable_cylinderEvent_apply (hi : i in Δ) : Measurable[cylinderEvents Δ
] fun f : forall i, X i => f i
参数：hi : i in Δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.measurable_cylinderEvents_iff`：measurable_cylinderEvents_i
ff {g : α -> forall i, X i} : @Measurable _ _ _ (cylinderEvents Δ) g ↔ forall ⦃i
⦄, i in Δ -> Measurable fun a => …
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
lemma measurable_cylinderEvent_apply (hi : i ∈ Δ) :
    Measurable[cylinderEvents Δ] fun f : ∀ i, X i => f i :=
  measurable_cylinderEvents_iff.1 measurable_id hi
/-
**MeasureTheory.Measurable.eval_cylinderEvents** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measurable`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {X : ι → Type u_3} {mα : MeasurableSpace α
} [m : (i : ι) → MeasurableSpace (X i)]   {Δ : Set ι} {i : ι} {g : α → (i : ι) →
 X i}, i ∈ Δ → Measurable g → Measurable fun a => g a i
参数：i : ι；X i；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用引理 `MeasureTheory.measurable_cylinderEvent_apply`：measurable_cylinderEvent_a
pply (hi : i in Δ) : Measurable[cylinderEvents Δ] fun f : forall i, X i => f i
-/
lemma Measurable.eval_cylinderEvents {g : α → ∀ i, X i} (hi : i ∈ Δ)
    (hg : @Measurable _ _ _ (cylinderEvents Δ) g) : Measurable fun a ↦ g a i :=
  (measurable_cylinderEvent_apply hi).comp hg

@[fun_prop]
/-
**MeasureTheory.measurable_cylinderEvents_lambda** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：measurable_cylinderEvents_lambda (f : α -> forall i, X i) (hf : forall i, 
Measurable fun a => f a i) : Measurable f
参数：f : α -> forall i, X i；hf : forall i, Measurable fun a => f a i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
-/
lemma measurable_cylinderEvents_lambda (f : α → ∀ i, X i) (hf : ∀ i, Measurable fun a ↦ f a i) :
    Measurable f :=
  measurable_pi_iff.mpr hf

/-- The function `(f, x) ↦ update f a x : (Π a, X a) × X a → Π a, X a` is measurable. -/
/-
**MeasureTheory.measurable_update_cylinderEvents'** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory`。
形式化陈述：measurable_update_cylinderEvents' [DecidableEq ι] : @Measurable _ _ (.prod
 (cylinderEvents Δ) (m i)) (cylinderEvents Δ) (fun p : (forall i, X i) × X i => 
update p.1 i p.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.measurable_cylinderEvents_iff`：measurable_cylinderEvents_i
ff {g : α -> forall i, X i} : @Measurable _ _ _ (cylinderEvents Δ) g ↔ forall ⦃i
⦄, i in Δ -> Measurable fun a => …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)

--- 原说明 ---
The function `(f, x) ↦ update f a x : (Π a, X a) × X a → Π a, X a` is measurable
.
-/
lemma measurable_update_cylinderEvents' [DecidableEq ι] :
    @Measurable _ _ (.prod (cylinderEvents Δ) (m i)) (cylinderEvents Δ)
      (fun p : (∀ i, X i) × X i ↦ update p.1 i p.2) := by
  rw [measurable_cylinderEvents_iff]
  intro j hj
  dsimp [update]
  split_ifs with h
  · subst h
    dsimp
    exact measurable_snd
  · exact measurable_cylinderEvents_iff.1 measurable_fst hj
/-
**MeasureTheory.measurable_uniqueElim_cylinderEvents** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory`。
形式化陈述：measurable_uniqueElim_cylinderEvents [Unique ι] : Measurable (uniqueElim :
 X (default : ι) -> forall i, X i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
lemma measurable_uniqueElim_cylinderEvents [Unique ι] :
    Measurable (uniqueElim : X (default : ι) → ∀ i, X i) := by
  simp_rw [measurable_pi_iff, Unique.forall_iff, uniqueElim_default]; exact measurable_id

/-- The function `update f a : X a → Π a, X a` is always measurable.
This doesn't require `f` to be measurable.
This should not be confused with the statement that `update f a x` is measurable. -/
@[fun_prop]
/-
**MeasureTheory.measurable_update_cylinderEvents** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：measurable_update_cylinderEvents (f : forall a : ι, X a) {a : ι} [Decidabl
eEq ι] : @Measurable _ _ _ (cylinderEvents Δ) (update f a)
参数：f : forall a : ι, X a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用引理 `MeasureTheory.measurable_update_cylinderEvents'`：measurable_update_cylin
derEvents' [DecidableEq ι] : @Measurable _ _ (.prod (cylinderEvents Δ) (m i)) (c
ylinderEvents Δ) (fun p : (forall i, …
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)

--- 原说明 ---
The function `update f a : X a → Π a, X a` is always measurable.
This doesn't require `f` to be measurable.
This should not be confused with the statement that `update f a x` is measurable
.
-/
lemma measurable_update_cylinderEvents (f : ∀ a : ι, X a) {a : ι} [DecidableEq ι] :
    @Measurable _ _ _ (cylinderEvents Δ) (update f a) :=
  measurable_update_cylinderEvents'.comp measurable_prodMk_left
/-
**MeasureTheory.measurable_update_cylinderEvents_left** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory`。
形式化陈述：measurable_update_cylinderEvents_left {a : ι} [DecidableEq ι] {x : X a} : 
@Measurable _ _ (cylinderEvents Δ) (cylinderEvents Δ) (update · a x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用引理 `MeasureTheory.measurable_update_cylinderEvents'`：measurable_update_cylin
derEvents' [DecidableEq ι] : @Measurable _ _ (.prod (cylinderEvents Δ) (m i)) (c
ylinderEvents Δ) (fun p : (forall i, …
· 使用定理 `measurable_prodMk_right`：measurable_prodMk_right {y : β} : Measurable fu
n x : α => (x, y)
-/
lemma measurable_update_cylinderEvents_left {a : ι} [DecidableEq ι] {x : X a} :
    @Measurable _ _ (cylinderEvents Δ) (cylinderEvents Δ) (update · a x) :=
  measurable_update_cylinderEvents'.comp measurable_prodMk_right
/-
**MeasureTheory.measurable_restrict_cylinderEvents** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory`。
形式化陈述：measurable_restrict_cylinderEvents (Δ : Set ι) : Measurable[cylinderEvents
 (X
参数：Δ : Set ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用引理 `MeasureTheory.measurable_cylinderEvent_apply`：measurable_cylinderEvent_a
pply (hi : i in Δ) : Measurable[cylinderEvents Δ] fun f : forall i, X i => f i
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma measurable_restrict_cylinderEvents (Δ : Set ι) :
    Measurable[cylinderEvents (X := X) Δ] (domRestrict Δ) := by
  rw [@measurable_pi_iff]; exact fun i ↦ measurable_cylinderEvent_apply i.2

end cylinderEvents

/-- A measurable set from the product sigma-algebra only depends on countably many coordinates. -/
/-
**MeasureTheory.MeasurableSet.eq_preimage_restrict_countable** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.MeasurableSet`。
形式化陈述：∀ {ι : Type u_2} {α : ι → Type u_1} [inst : (i : ι) → MeasurableSpace (α i
)] {s : Set ((i : ι) → α i)},   MeasurableSet s → ∃ I t, I.Countable ∧ s = I.dom
Restrict ⁻¹' t
参数：i : ι；α i；(i : ι) → α i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.generateFrom_squareCylinders`：generateFrom_squareCylinders
 [forall i, MeasurableSpace (α i)] : MeasurableSpace.generateFrom (squareCylinde
rs fun i => {s : Set (α i) | Mea…
· 使用定理 `MeasureTheory.isPiSystem_squareCylinders`：isPiSystem_squareCylinders {C 
: forall i, Set (Set (α i))} (hC : forall i, IsPiSystem (C i)) (hC_univ : forall
 i, univ in C i) : IsPiSystem …
· 使用定理 `MeasurableSpace.isPiSystem_measurableSet`：isPiSystem_measurableSet {α : 
Type*} [MeasurableSpace α] : IsPiSystem { s : Set α | MeasurableSet s }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.countable_iUnion`：countable_iUnion {t : ι -> Set α} [Countable ι] (h
t : forall i, (t i).Countable) : (⋃ i, t i).Countable
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
A measurable set from the product sigma-algebra only depends on countably many c
oordinates.
-/
lemma MeasurableSet.eq_preimage_restrict_countable
    [∀ i, MeasurableSpace (α i)] {s : Set (Π i, α i)} (hs : MeasurableSet s) :
    ∃ I : Set ι, ∃ t, I.Countable ∧ s = I.domRestrict ⁻¹' t := by
  refine induction_on_inter generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ ↦ isPiSystem_measurableSet) (by simp))
    ⟨∅, ∅, by simp⟩ ?_ ?_ ?_ s hs
  · rintro - ⟨I, t, -, rfl⟩
    exact ⟨I, univ.pi (fun i ↦ t i), I.countable_toSet, by ext; simp⟩
  · rintro - - ⟨I, t, hI, rfl⟩
    exact ⟨I, tᶜ, hI, by simp⟩
  intro f df mf hf
  choose! I t hI hf using hf
  refine ⟨⋃ n, I n, ⋃ n, (⋃ k, I k).domRestrict '' (f n), countable_iUnion hI, ?_⟩
  ext x
  simp only [hf, mem_iUnion, mem_preimage, preimage_iUnion, mem_image]
  refine ⟨fun ⟨i, hi⟩ ↦ ⟨i, x, hi, rfl⟩, fun ⟨n, x', hn, hx⟩ ↦ ⟨n, ?_⟩⟩
  have (x : Π i, α i) : (I n).domRestrict x =
      (fun (x : Π (i : ⋃ k, I k), α i) (i : I n) ↦ x ⟨i.1, subset_iUnion I n i.2⟩)
      ((⋃ k, I k).domRestrict x) := rfl
  rwa [this, ← hx, ← this]

end MeasureTheory

