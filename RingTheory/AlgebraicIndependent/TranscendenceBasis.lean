/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Combinatorics.Matroid.Rank.Cardinal
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Transcendence basis

This file defines the transcendence basis as a maximal algebraically independent subset.

## Main results

* `exists_isTranscendenceBasis`: a ring extension has a transcendence basis
* `IsTranscendenceBasis.lift_cardinalMk_eq_trdeg`: any transcendence basis of a domain has
  cardinality equal to transcendental degree.
* `IsTranscendenceBasis.lift_cardinalMk_eq`: any two transcendence bases of a domain have the
  same cardinality.

## References

* [Stacks: Transcendence](https://stacks.math.columbia.edu/tag/030D)

## Tags
transcendence basis, transcendence degree, transcendence

-/

@[expose] public section

noncomputable section

open Function Set Subalgebra MvPolynomial Algebra

universe u u' v w

variable {ι : Type u} {ι' : Type u'} (R : Type*) {S : Type v} {A : Type w}
variable {x : ι → A} {y : ι' → A}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

open AlgebraicIndependent

variable {R} in
/-
**exists_isTranscendenceBasis_superset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isTranscendenceBasis_superset {s : Set A} (hs : AlgebraicIndepOn R 
id s) : exists t, s subseteq t ∧ IsTranscendenceBasis R ((↑) : t -> A)
参数：hs : AlgebraicIndepOn R id s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `exists_maximal_algebraicIndependent`：exists_maximal_algebraicIndependent
 (s t : Set A) (hst : s subseteq t) (hs : AlgebraicIndepOn R id s) : exists u, s
 subseteq u ∧ Maximal (fu…
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem exists_isTranscendenceBasis_superset {s : Set A}
    (hs : AlgebraicIndepOn R id s) :
    ∃ t, s ⊆ t ∧ IsTranscendenceBasis R ((↑) : t → A) := by
  simpa [← isTranscendenceBasis_iff_maximal]
    using exists_maximal_algebraicIndependent s _ (subset_univ _) hs

variable (A)
/-
**exists_isTranscendenceBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isTranscendenceBasis [FaithfulSMul R A] : exists s : Set A, IsTrans
cendenceBasis R ((↑) : s -> A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_isTranscendenceBasis_superset`：exists_isTranscendenceBasis_supers
et {s : Set A} (hs : AlgebraicIndepOn R id s) : exists t, s subseteq t ∧ IsTrans
cendenceBasis R ((↑) : t -…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `algebraicIndependent_empty_iff`：algebraicIndependent_empty_iff : Algebra
icIndependent R ((↑) : (∅ : Set A) -> A) ↔ Injective (algebraMap R A)
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
theorem exists_isTranscendenceBasis [FaithfulSMul R A] :
    ∃ s : Set A, IsTranscendenceBasis R ((↑) : s → A) := by
  simpa using exists_isTranscendenceBasis_superset
    ((algebraicIndependent_empty_iff R A).mpr (FaithfulSMul.algebraMap_injective R A))

/-- `Type` version of `exists_isTranscendenceBasis`. -/
/-
**exists_isTranscendenceBasis'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isTranscendenceBasis' [FaithfulSMul R A] : exists (ι : Type w) (x :
 ι -> A), IsTranscendenceBasis R x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_isTranscendenceBasis`：exists_isTranscendenceBasis [FaithfulSMul R
 A] : exists s : Set A, IsTranscendenceBasis R ((↑) : s -> A)

--- 原说明 ---
`Type` version of `exists_isTranscendenceBasis`.
-/
theorem exists_isTranscendenceBasis' [FaithfulSMul R A] :
    ∃ (ι : Type w) (x : ι → A), IsTranscendenceBasis R x :=
  have ⟨s, h⟩ := exists_isTranscendenceBasis R A
  ⟨s, Subtype.val, h⟩

variable {A}

open Cardinal in
/-
**trdeg_eq_iSup_cardinalMk_isTranscendenceBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trdeg_eq_iSup_cardinalMk_isTranscendenceBasis : trdeg R A = ⨆ ι : { s : Se
t A // IsTranscendenceBasis R ((↑) : s -> A) }, #ι.1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `exists_isTranscendenceBasis_superset`：exists_isTranscendenceBasis_supers
et {s : Set A} (hs : AlgebraicIndepOn R id s) : exists t, s subseteq t ∧ IsTrans
cendenceBasis R ((↑) : t -…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem trdeg_eq_iSup_cardinalMk_isTranscendenceBasis :
    trdeg R A = ⨆ ι : { s : Set A // IsTranscendenceBasis R ((↑) : s → A) }, #ι.1 := by
  refine (ciSup_le' fun s ↦ ?_).antisymm
    (ciSup_le' fun s ↦ le_ciSup_of_le bddAbove_of_small ⟨s, s.2.1⟩ le_rfl)
  choose t ht using exists_isTranscendenceBasis_superset s.2
  exact le_ciSup_of_le bddAbove_of_small ⟨t, ht.2⟩ (mk_le_mk_of_subset ht.1)

variable {R}
/-
**AlgebraicIndependent.isTranscendenceBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.isTranscendenceBasis_iff [Nontrivial R] (i : Algebrai
cIndependent R x) : IsTranscendenceBasis R x ↔ forall (κ : Type w) (w : κ -> A) 
(_ : AlgebraicIndependent R w) (j : ι -> κ) (_ : w ∘ j = x), Surjective j
参数：i : AlgebraicIndependent R x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `AlgebraicIndependent.coe_range`：coe_range : AlgebraicIndependent R ((↑) 
: range x -> A)
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_injective`：image_injective : Injective (image f) ↔ Injective f
· 使用定理 `AlgebraicIndependent.injective`：∀ {ι : Type u} {R : Type u_2} {A : Type 
v} {x : ι → A} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],
   AlgebraicIndepend…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem AlgebraicIndependent.isTranscendenceBasis_iff [Nontrivial R]
    (i : AlgebraicIndependent R x) :
    IsTranscendenceBasis R x ↔
      ∀ (κ : Type w) (w : κ → A) (_ : AlgebraicIndependent R w) (j : ι → κ) (_ : w ∘ j = x),
        Surjective j := by
  fconstructor
  · rintro p κ w i' j rfl
    have p := p.2 (range w) i'.coe_range (range_comp_subset_range _ _)
    rw [range_comp, ← @image_univ _ _ w] at p
    exact range_eq_univ.mp (image_injective.mpr i'.injective p)
  · intro p
    use i
    intro w i' h
    specialize p w ((↑) : w → A) i' (fun i => ⟨x i, range_subset_iff.mp h i⟩) (by ext; simp)
    have q := congr_arg (fun s => ((↑) : w → A) '' s) p.range_eq
    rw [← image_univ, image_image] at q
    simpa using q
/-
**IsTranscendenceBasis.isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTranscendenceBasis.isAlgebraic [Nontrivial R] (hx : IsTranscendenceBasis
 R x) : Algebra.IsAlgebraic (adjoin R (range x)) A
参数：hx : IsTranscendenceBasis R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `AlgebraicIndependent.option_iff_transcendental`：AlgebraicIndependent.opt
ion_iff_transcendental (hx : AlgebraicIndependent R x) (a : A) : AlgebraicIndepe
ndent R (fun o : Option ι => o.elim …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `AlgebraicIndependent.injective`：∀ {ι : Type u} {R : Type u_2} {A : Type 
v} {x : ι → A} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],
   AlgebraicIndepend…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `algebraicIndependent_subtype_range`：algebraicIndependent_subtype_range {
ι} {f : ι -> A} (hf : Injective f) : AlgebraicIndependent R ((↑) : range f -> A)
 ↔ AlgebraicIndependent …
-/
theorem IsTranscendenceBasis.isAlgebraic [Nontrivial R] (hx : IsTranscendenceBasis R x) :
    Algebra.IsAlgebraic (adjoin R (range x)) A := by
  constructor
  intro a
  rw [← not_iff_comm.1 (hx.1.option_iff_transcendental _).symm]
  intro ai
  have h₁ : range x ⊆ range fun o : Option ι => o.elim a x := by
    rintro x ⟨y, rfl⟩
    exact ⟨some y, rfl⟩
  have h₂ : range x ≠ range fun o : Option ι => o.elim a x := by
    intro h
    have : a ∈ range x := by
      rw [h]
      exact ⟨none, rfl⟩
    rcases this with ⟨b, rfl⟩
    have : some b = none := ai.injective rfl
    simpa
  exact h₂ (hx.2 (Set.range fun o : Option ι => o.elim a x)
    ((algebraicIndependent_subtype_range ai.injective).2 ai) h₁)
/-
**AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic [Nontrivial R] (
ind : AlgebraicIndependent R x) : IsTranscendenceBasis R x ↔ Algebra.IsAlgebraic
 (adjoin R (range x)) A
参数：ind : AlgebraicIndependent R x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTranscendenceBasis.isAlgebraic`：IsTranscendenceBasis.isAlgebraic [Nont
rivial R] (hx : IsTranscendenceBasis R x) : Algebra.IsAlgebraic (adjoin R (range
 x)) A
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用定理 `AlgebraicIndependent.transcendental_adjoin`：transcendental_adjoin {s : S
et ι} {i : ι} (hi : i ∉ s) : Transcendental (adjoin R (x '' s)) (x i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.range_inclusion`：range_inclusion (h : s subseteq t) : range (inclusi
on h) = { x : t | (x : α) in s }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Set.val_comp_inclusion`：val_comp_inclusion (h : s subseteq t) : Subtype.
val ∘ inclusion h = Subtype.val
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
-/
theorem AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic
    [Nontrivial R] (ind : AlgebraicIndependent R x) :
    IsTranscendenceBasis R x ↔ Algebra.IsAlgebraic (adjoin R (range x)) A := by
  refine ⟨(·.isAlgebraic), fun alg ↦ ⟨ind, fun s ind_s hxs ↦ of_not_not fun hxs' ↦ ?_⟩⟩
  have : ¬ s ⊆ range x := (hxs' <| hxs.antisymm ·)
  have ⟨a, has, hax⟩ := not_subset.mp this
  rw [show range x = Subtype.val '' range (Set.inclusion hxs) by
    rw [← range_comp, val_comp_inclusion, Subtype.range_val]] at alg
  refine ind_s.transcendental_adjoin (s := range (inclusion hxs)) (i := ⟨a, has⟩) ?_ (alg.1 _)
  simpa using hax
/-
**isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic [Nontrivial R] :
 IsTranscendenceBasis R x ↔ AlgebraicIndependent R x ∧ Algebra.IsAlgebraic (adjo
in R (range x)) A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic`：AlgebraicInde
pendent.isTranscendenceBasis_iff_isAlgebraic [Nontrivial R] (ind : AlgebraicInde
pendent R x) : IsTranscendenceBasis R x ↔ Algeb…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic [Nontrivial R] :
    IsTranscendenceBasis R x ↔
      AlgebraicIndependent R x ∧ Algebra.IsAlgebraic (adjoin R (range x)) A :=
  ⟨fun h ↦ ⟨h.1, h.1.isTranscendenceBasis_iff_isAlgebraic.mp h⟩,
    fun ⟨ind, alg⟩ ↦ ind.isTranscendenceBasis_iff_isAlgebraic.mpr alg⟩
/-
**IsTranscendenceBasis.algebraMap_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsTranscendenceBasis.algebraMap_comp [Nontrivial R] [NoZeroDivisors S] [Al
gebra.IsAlgebraic S A] [FaithfulSMul S A] {x : ι -> S} (hx : IsTranscendenceBasi
s R x) : IsTranscendenceBasis R (algebraMap S A ∘ x)
参数：hx : IsTranscendenceBasis R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic`：AlgebraicInde
pendent.isTranscendenceBasis_iff_isAlgebraic [Nontrivial R] (ind : AlgebraicInde
pendent R x) : IsTranscendenceBasis R x ↔ Algeb…
· 使用定理 `AlgebraicIndependent.map`：map {f : A ->ₐ[R] A'} (hf_inj : Set.InjOn f (a
djoin R (range x))) : AlgebraicIndependent R (f ∘ x)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.map_adjoin`：map_adjoin (φ : A ->ₐ[R] B) (s : Set A) : (adjoin R s
).map φ = adjoin R (φ '' s)
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `IsTranscendenceBasis.isAlgebraic`：IsTranscendenceBasis.isAlgebraic [Nont
rivial R] (hx : IsTranscendenceBasis R x) : Algebra.IsAlgebraic (adjoin R (range
 x)) A
· 使用定理 `Algebra.IsAlgebraic.trans`：∀ (R : Type u_1) (S : Type u_2) (A : Type u_3
) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebr
a R S] [inst_4 …
· 使用定理 `Algebra.IsAlgebraic.extendScalars`：Algebra.IsAlgebraic.extendScalars (hi
nj : Function.Injective (algebraMap R S)) [Algebra.IsAlgebraic R A] : Algebra.Is
Algebraic S A
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
-/
lemma IsTranscendenceBasis.algebraMap_comp
    [Nontrivial R] [NoZeroDivisors S] [Algebra.IsAlgebraic S A] [FaithfulSMul S A]
    {x : ι → S} (hx : IsTranscendenceBasis R x) : IsTranscendenceBasis R (algebraMap S A ∘ x) := by
  let f := IsScalarTower.toAlgHom R S A
  refine hx.1.map (f := f) (FaithfulSMul.algebraMap_injective S A).injOn
    |>.isTranscendenceBasis_iff_isAlgebraic.mpr ?_
  rw [Set.range_comp, ← AlgHom.map_adjoin]
  set Rx := adjoin R (range x)
  let e := Rx.equivMapOfInjective f (FaithfulSMul.algebraMap_injective S A)
  let := e.toRingHom.toAlgebra
  have : IsScalarTower Rx (Rx.map f) A := .of_algebraMap_eq fun x ↦ rfl
  have : Algebra.IsAlgebraic Rx S := hx.isAlgebraic
  have : Algebra.IsAlgebraic Rx A := .trans _ S _
  exact .extendScalars e.injective
/-
**IsTranscendenceBasis.isAlgebraic_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsTranscendenceBasis.isAlgebraic_iff [IsDomain S] [NoZeroDivisors A] {ι : 
Type*} {v : ι -> A} (hv : IsTranscendenceBasis R v) : Algebra.IsAlgebraic S A ↔ 
forall i, IsAlgebraic S (v i)
参数：hv : IsTranscendenceBasis R v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Subalgebra.restrictScalars_adjoin`：∀ (R : Type uR) {S : Type uS}
 {A : Type uA} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semir
ing A]   [inst_3 : Algebra R S]…
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsTranscendenceBasis.isAlgebraic`：IsTranscendenceBasis.isAlgebraic [Nont
rivial R] (hx : IsTranscendenceBasis R x) : Algebra.IsAlgebraic (adjoin R (range
 x)) A
· 使用定理 `Algebra.IsAlgebraic.extendScalars`：Algebra.IsAlgebraic.extendScalars (hi
nj : Function.Injective (algebraMap R S)) [Algebra.IsAlgebraic R A] : Algebra.Is
Algebraic S A
· 使用定理 `Subalgebra.inclusion_injective`：inclusion_injective : Function.Injective
 (inclusion h)
· 使用定理 `Algebra.IsAlgebraic.trans`：∀ (R : Type u_1) (S : Type u_2) (A : Type u_3
) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebr
a R S] [inst_4 …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma IsTranscendenceBasis.isAlgebraic_iff [IsDomain S] [NoZeroDivisors A]
    {ι : Type*} {v : ι → A} (hv : IsTranscendenceBasis R v) :
    Algebra.IsAlgebraic S A ↔ ∀ i, IsAlgebraic S (v i) := by
  refine ⟨fun _ i ↦ Algebra.IsAlgebraic.isAlgebraic (v i), fun H ↦ ?_⟩
  let Rv := adjoin R (range v)
  let Sv := adjoin S (range v)
  have : Algebra.IsAlgebraic S Sv := by
    simpa [Sv, ← Subalgebra.isAlgebraic_iff, isAlgebraic_adjoin_iff]
  have le : Rv ≤ Sv.restrictScalars R := by
    rw [Subalgebra.restrictScalars_adjoin]; exact le_sup_right
  let : Algebra Rv Sv := (Subalgebra.inclusion le).toAlgebra
  have : IsScalarTower Rv Sv A := .of_algebraMap_eq fun x ↦ rfl
  have := (algebraMap R S).domain_nontrivial
  have := hv.isAlgebraic
  have : Algebra.IsAlgebraic Sv A := .extendScalars (Subalgebra.inclusion_injective le)
  exact .trans _ Sv _

variable (ι R)
/-
**IsTranscendenceBasis.mvPolynomial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTranscendenceBasis.mvPolynomial [Nontrivial R] : IsTranscendenceBasis R 
(X (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic`：isTranscenden
ceBasis_iff_algebraicIndependent_isAlgebraic [Nontrivial R] : IsTranscendenceBas
is R x ↔ AlgebraicIndependent R x ∧ Algebra.IsA…
· 使用定理 `MvPolynomial.algebraicIndependent_X`：MvPolynomial.algebraicIndependent_X
 (σ R : Type*) [CommRing R] : AlgebraicIndependent R (X (R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.adjoin_range_X`：adjoin_range_X : Algebra.adjoin R (range (X
 : σ -> MvPolynomial σ R)) = ⊤
· 使用引理 `Algebra.isIntegral_of_surjective`：Algebra.isIntegral_of_surjective (H : 
Function.Surjective (algebraMap R B)) : Algebra.IsIntegral R B
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
theorem IsTranscendenceBasis.mvPolynomial [Nontrivial R] :
    IsTranscendenceBasis R (X (R := R) (σ := ι)) := by
  refine isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.2 ⟨algebraicIndependent_X .., ?_⟩
  rw [adjoin_range_X]
  set A := MvPolynomial ι R
  have := Algebra.isIntegral_of_surjective (R := (⊤ : Subalgebra R A)) (B := A) (⟨⟨·, ⟨⟩⟩, rfl⟩)
  infer_instance
/-
**IsTranscendenceBasis.mvPolynomial'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTranscendenceBasis.mvPolynomial' [Nonempty ι] : IsTranscendenceBasis R (
X (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTranscendenceBasis.mvPolynomial`：IsTranscendenceBasis.mvPolynomial [No
ntrivial R] : IsTranscendenceBasis R (X (R
-/
theorem IsTranscendenceBasis.mvPolynomial' [Nonempty ι] :
    IsTranscendenceBasis R (X (R := R) (σ := ι)) := by nontriviality R; exact .mvPolynomial ι R
/-
**IsTranscendenceBasis.polynomial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTranscendenceBasis.polynomial [Nonempty ι] [Subsingleton ι] : IsTranscen
denceBasis R fun _ : ι => (.X : Polynomial R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `nonempty_unique`：nonempty_unique (α : Sort u) [Subsingleton α] [Nonempty
 α] : Nonempty (Unique α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `isTranscendenceBasis_equiv`：isTranscendenceBasis_equiv (e : ι ≃ ι') {f :
 ι' -> A} : IsTranscendenceBasis R (f ∘ e) ↔ IsTranscendenceBasis R f
· 使用定理 `AlgEquiv.isTranscendenceBasis_iff`：AlgEquiv.isTranscendenceBasis_iff (e 
: A ≃ₐ[R] A') : IsTranscendenceBasis R (e ∘ x) ↔ IsTranscendenceBasis R x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.uniqueAlgEquiv_symm_apply`：∀ (R : Type u) [inst : CommSemir
ing R] (σ : Type u_2) [inst_1 : Unique σ] (p : Polynomial R),   (MvPolynomial.un
iqueAlgEquiv R σ).symm p = P…
· 使用定理 `Polynomial.eval₂_X`：eval₂_X : X.eval₂ f x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsTranscendenceBasis.mvPolynomial`：IsTranscendenceBasis.mvPolynomial [No
ntrivial R] : IsTranscendenceBasis R (X (R
-/
theorem IsTranscendenceBasis.polynomial [Nonempty ι] [Subsingleton ι] :
    IsTranscendenceBasis R fun _ : ι ↦ (.X : Polynomial R) := by
  nontriviality R
  have := (nonempty_unique ι).some
  refine (isTranscendenceBasis_equiv (Equiv.equivPUnit.{_, 1} _).symm).mp <|
    (MvPolynomial.uniqueAlgEquiv R PUnit).symm.isTranscendenceBasis_iff.mp ?_
  convert! IsTranscendenceBasis.mvPolynomial PUnit R
  ext; simp

variable {ι R}
/-
**IsTranscendenceBasis.sumElim_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTranscendenceBasis.sumElim_comp [NoZeroDivisors A] {x : ι -> S} {y : ι' 
-> A} (hx : IsTranscendenceBasis R x) (hy : IsTranscendenceBasis S y) : IsTransc
endenceBasis R (Sum.elim y (algebraMap S A ∘ x))
参数：hx : IsTranscendenceBasis R x；hy : IsTranscendenceBasis S y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isTranscendenceBasis_iff_of_subsingleton`：isTranscendenceBasis_iff_of_su
bsingleton [Subsingleton R] (x : ι -> A) : IsTranscendenceBasis R x ↔ Nonempty ι
· 使用定理 `Sum.nonemptyRight`：∀ {α : Type u} {β : Type v} [h : Nonempty β], Nonempt
y (α ⊕ β)
· 使用定理 `AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic`：AlgebraicInde
pendent.isTranscendenceBasis_iff_isAlgebraic [Nontrivial R] (ind : AlgebraicInde
pendent R x) : IsTranscendenceBasis R x ↔ Algeb…
· 使用定理 `AlgebraicIndependent.sumElim_comp`：sumElim_comp {ι'} {x : ι -> S} {y : ι
' -> A} (hx : AlgebraicIndependent R x) (hy : AlgebraicIndependent S y) : Algebr
aicIndependent R (Sum.e…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_algebraMap_image_union_eq_adjoin_adjoin`：adjoin_algebraMa
p_image_union_eq_adjoin_adjoin (s : Set S) (t : Set A) : adjoin R (algebraMap S 
A '' s union t) = (adjoin (adjoin R s) t).re…
· 使用定理 `Set.Sum.elim_range`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : 
α → γ) (g : β → γ),   Set.range (Sum.elim f g) = Set.range f ∪ Set.range g
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `AlgebraicIndependent.algebraMap_injective`：algebraMap_injective : Inject
ive (algebraMap R A)
· 使用定理 `IsTranscendenceBasis.isAlgebraic`：IsTranscendenceBasis.isAlgebraic [Nont
rivial R] (hx : IsTranscendenceBasis R x) : Algebra.IsAlgebraic (adjoin R (range
 x)) A
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Algebra.adjoin_induction`：adjoin_induction {p : (x : A) -> x in adjoin R
 s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_adjoin hx)) (algebraMap
 : forall r, p…
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `IsAlgebraic.extendScalars`：IsAlgebraic.extendScalars (hinj : Function.In
jective (algebraMap R S)) {x : A} (A_alg : IsAlgebraic R x) : IsAlgebraic S x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `IsAlgebraic.algHom`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] {B : Type u_2}   [inst_3 : Ring B] [inst_4 
: Algebr…
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
（共 33 条，此处仅展示前 30 条）
-/
theorem IsTranscendenceBasis.sumElim_comp [NoZeroDivisors A] {x : ι → S} {y : ι' → A}
    (hx : IsTranscendenceBasis R x) (hy : IsTranscendenceBasis S y) :
    IsTranscendenceBasis R (Sum.elim y (algebraMap S A ∘ x)) := by
  cases subsingleton_or_nontrivial R
  · rw [isTranscendenceBasis_iff_of_subsingleton] at hx ⊢; infer_instance
  rw [(hx.1.sumElim_comp hy.1).isTranscendenceBasis_iff_isAlgebraic]
  set Rx := adjoin R (range x)
  let Rxy := adjoin Rx (range y)
  rw [show adjoin R (range <| Sum.elim y (algebraMap S A ∘ x)) = Rxy.restrictScalars R by
    rw [← adjoin_algebraMap_image_union_eq_adjoin_adjoin, Sum.elim_range, union_comm, range_comp]]
  change Algebra.IsAlgebraic Rxy A
  have := hx.1.algebraMap_injective.nontrivial
  have := hy.1.algebraMap_injective.nontrivial
  have := hy.isAlgebraic
  set Sy := adjoin S (range y)
  let _ : Algebra Rxy Sy := by
    refine (Subalgebra.inclusion (T := Sy.restrictScalars Rx) <| adjoin_le ?_).toAlgebra
    rintro _ ⟨i, rfl⟩; exact subset_adjoin (s := range y) ⟨i, rfl⟩
  have : IsScalarTower Rxy Sy A := .of_algebraMap_eq fun ⟨a, _⟩ ↦ show a = _ from rfl
  have : IsScalarTower Rx Rxy Sy := .of_algebraMap_eq fun ⟨a, _⟩ ↦ Subtype.ext rfl
  have : Algebra.IsAlgebraic Rxy Sy := by
    refine ⟨fun ⟨a, ha⟩ ↦ adjoin_induction ?_ (fun _ ↦ .extendScalars (R := Rx) ?_ ?_)
      (fun _ _ _ _ ↦ .add) (fun _ _ _ _ ↦ .mul) ha⟩
    · rintro _ ⟨i, rfl⟩; exact isAlgebraic_algebraMap (⟨y i, subset_adjoin ⟨i, rfl⟩⟩ : Rxy)
    · exact fun _ _ ↦ (Subtype.ext <| hy.1.algebraMap_injective <| Subtype.ext_iff.mp ·)
    · exact (hx.isAlgebraic.1 _).algHom (IsScalarTower.toAlgHom Rx S Sy)
  exact .trans _ Sy _

/-- If `x` is a transcendence basis of `A/R`, then it is empty if and only if
`A/R` is algebraic. -/
/-
**IsTranscendenceBasis.isEmpty_iff_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTranscendenceBasis.isEmpty_iff_isAlgebraic [Nontrivial R] (hx : IsTransc
endenceBasis R x) : IsEmpty ι ↔ Algebra.IsAlgebraic R A
参数：hx : IsTranscendenceBasis R x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTranscendenceBasis.isAlgebraic`：IsTranscendenceBasis.isAlgebraic [Nont
rivial R] (hx : IsTranscendenceBasis R x) : Algebra.IsAlgebraic (adjoin R (range
 x)) A
· 使用定理 `Subalgebra.algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left`：algebra_
isAlgebraic_of_algebra_isAlgebraic_bot_left [Algebra.IsAlgebraic (⊥ : Subalgebra
 R S) S] : Algebra.IsAlgebraic R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin_empty`：adjoin_empty : adjoin R (∅ : Set A) = ⊥
· 使用定理 `Set.range_eq_empty`：range_eq_empty [IsEmpty ι] (f : ι -> α) : range f = 
∅
· 使用定理 `AlgebraicIndependent.isEmpty_of_isAlgebraic`：isEmpty_of_isAlgebraic [Alg
ebra.IsAlgebraic R A] : IsEmpty ι
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If `x` is a transcendence basis of `A/R`, then it is empty if and only if
`A/R` is algebraic.
-/
theorem IsTranscendenceBasis.isEmpty_iff_isAlgebraic [Nontrivial R]
    (hx : IsTranscendenceBasis R x) :
    IsEmpty ι ↔ Algebra.IsAlgebraic R A := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ hx.1.isEmpty_of_isAlgebraic⟩
  have := hx.isAlgebraic
  rw [Set.range_eq_empty x, adjoin_empty] at this
  exact algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left R A

/-- If `x` is a transcendence basis of `A/R`, then it is not empty if and only if
`A/R` is transcendental. -/
/-
**IsTranscendenceBasis.nonempty_iff_transcendental** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTranscendenceBasis.nonempty_iff_transcendental [Nontrivial R] (hx : IsTr
anscendenceBasis R x) : Nonempty ι ↔ Algebra.Transcendental R A
参数：hx : IsTranscendenceBasis R x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
· 使用定理 `Algebra.transcendental_iff_not_isAlgebraic`：Algebra.transcendental_iff_n
ot_isAlgebraic : Algebra.Transcendental R A ↔ ¬ Algebra.IsAlgebraic R A
· 使用定理 `IsTranscendenceBasis.isEmpty_iff_isAlgebraic`：IsTranscendenceBasis.isEmp
ty_iff_isAlgebraic [Nontrivial R] (hx : IsTranscendenceBasis R x) : IsEmpty ι ↔ 
Algebra.IsAlgebraic R A
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If `x` is a transcendence basis of `A/R`, then it is not empty if and only if
`A/R` is transcendental.
-/
theorem IsTranscendenceBasis.nonempty_iff_transcendental [Nontrivial R]
    (hx : IsTranscendenceBasis R x) :
    Nonempty ι ↔ Algebra.Transcendental R A := by
  rw [← not_isEmpty_iff, Algebra.transcendental_iff_not_isAlgebraic, hx.isEmpty_iff_isAlgebraic]
/-
**IsTranscendenceBasis.isAlgebraic_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTranscendenceBasis.isAlgebraic_field {F E : Type*} {x : ι -> E} [Field F
] [Field E] [Algebra F E] (hx : IsTranscendenceBasis F x) : Algebra.IsAlgebraic 
(IntermediateField.adjoin F (range x)) E
参数：hx : IsTranscendenceBasis F x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTranscendenceBasis.isAlgebraic`：IsTranscendenceBasis.isAlgebraic [Nont
rivial R] (hx : IsTranscendenceBasis R x) : Algebra.IsAlgebraic (adjoin R (range
 x)) A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.algebra_adjoin_le_adjoin`：algebra_adjoin_le_adjoin : A
lgebra.adjoin F S <= (adjoin F S).toSubalgebra
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Algebra.IsAlgebraic.extendScalars`：Algebra.IsAlgebraic.extendScalars (hi
nj : Function.Injective (algebraMap R S)) [Algebra.IsAlgebraic R A] : Algebra.Is
Algebraic S A
· 使用定理 `Subalgebra.inclusion_injective`：inclusion_injective : Function.Injective
 (inclusion h)
-/
theorem IsTranscendenceBasis.isAlgebraic_field {F E : Type*} {x : ι → E}
    [Field F] [Field E] [Algebra F E] (hx : IsTranscendenceBasis F x) :
    Algebra.IsAlgebraic (IntermediateField.adjoin F (range x)) E := by
  have := hx.isAlgebraic
  set S := range x
  let : Algebra (adjoin F S) (IntermediateField.adjoin F S) :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin F S)).toRingHom.toAlgebra
  have : IsScalarTower (adjoin F S) (IntermediateField.adjoin F S) E :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact Algebra.IsAlgebraic.extendScalars (R := adjoin F S) (Subalgebra.inclusion_injective _)

namespace AlgebraicIndependent

variable (R A) [FaithfulSMul R A]

section

variable [NoZeroDivisors A]

set_option backward.privateInPublic true in
/-
**AlgebraicIndependent.indepMatroid** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicIndepend
ent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def indepMatroid : IndepMatroid A where
  E := univ
  Indep := AlgebraicIndepOn R id
  indep_empty := (algebraicIndependent_empty_iff ..).mpr (FaithfulSMul.algebraMap_injective R A)
  indep_subset _ _ := (·.mono)
  indep_aug I B I_ind h B_base := by
    contrapose! h
    rw [← isTranscendenceBasis_iff_maximal] at B_base ⊢
    cases subsingleton_or_nontrivial R
    · rw [isTranscendenceBasis_iff_of_subsingleton] at B_base ⊢
      by_contra this
      have ⟨b, hb⟩ := B_base
      exact h b ⟨hb, fun hbI ↦ this ⟨b, hbI⟩⟩ .of_subsingleton
    apply I_ind.isTranscendenceBasis_iff_isAlgebraic.mpr
    replace B_base := B_base.isAlgebraic
    simp_rw +instances [id_eq]
    rw [Subtype.range_val] at B_base ⊢
    refine ⟨fun a ↦ (B_base.1 a).adjoin_of_forall_isAlgebraic fun x hx ↦ ?_⟩
    contrapose! h
    exact ⟨x, hx, I_ind.insert <| by rwa [image_id]⟩
  indep_maximal X _ I ind hIX := exists_maximal_algebraicIndependent I X hIX ind
  subset_ground _ _ := subset_univ _

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `R` is a commutative ring and `A` is a commutative `R`-algebra with injective algebra map
and no zero-divisors, then the `R`-algebraic independent subsets of `A` form a matroid. -/
/-
**AlgebraicIndependent.matroid** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicIndependent`。
形式化陈述：matroid : Matroid A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is a commutative ring and `A` is a commutative `R`-algebra with injective
 algebra map
and no zero-divisors, then the `R`-algebraic independent subsets of `A` form a m
atroid.
-/
def matroid : Matroid A := (indepMatroid R A).matroid.copyBase univ
  (fun s ↦ IsTranscendenceBasis R ((↑) : s → A)) rfl
  (fun B ↦ by simp_rw [Matroid.isBase_iff_maximal_indep, isTranscendenceBasis_iff_maximal]; rfl)
/-
**AlgebraicIndependent.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicIndependent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (matroid R A).Finitary where
  indep_of_forall_finite := algebraicIndependent_of_finite
/-
**AlgebraicIndependent.matroid_e** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicIndependent
`。
形式化陈述：∀ (R : Type u_1) (A : Type w) [inst : CommRing R] [inst_1 : CommRing A] [i
nst_2 : Algebra R A]   [inst_3 : FaithfulSMul R A] [inst_4 : NoZeroDivisors A], 
(AlgebraicIndependent.matroid R A).E = Set.univ
参数：R : Type u_1；A : Type w；AlgebraicIndependent.matroid R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem matroid_e : (matroid R A).E = univ := rfl
/-
**AlgebraicIndependent.matroid_cRank_eq** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicInde
pendent`。
形式化陈述：matroid_cRank_eq : (matroid R A).cRank = trdeg R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `trdeg_eq_iSup_cardinalMk_isTranscendenceBasis`：trdeg_eq_iSup_cardinalMk_
isTranscendenceBasis : trdeg R A = ⨆ ι : { s : Set A // IsTranscendenceBasis R (
(↑) : s -> A) }, #ι.1
-/
theorem matroid_cRank_eq : (matroid R A).cRank = trdeg R A :=
  (trdeg_eq_iSup_cardinalMk_isTranscendenceBasis _).symm

variable {R A}
/-
**AlgebraicIndependent.matroid_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicInd
ependent`。
形式化陈述：matroid_indep_iff {s : Set A} : (matroid R A).Indep s ↔ AlgebraicIndepOn R
 id s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem matroid_indep_iff {s : Set A} :
    (matroid R A).Indep s ↔ AlgebraicIndepOn R id s := Iff.rfl
/-
**AlgebraicIndependent.matroid_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicIn
dependent`。
形式化陈述：matroid_isBase_iff {s : Set A} : (matroid R A).IsBase s ↔ IsTranscendenceB
asis R ((↑) : s -> A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem matroid_isBase_iff {s : Set A} :
    (matroid R A).IsBase s ↔ IsTranscendenceBasis R ((↑) : s → A) := Iff.rfl

end

variable {R A}

/-
**AlgebraicIndependent.matroid_isBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicI
ndependent`。
形式化陈述：matroid_isBasis_iff [IsDomain A] {s t : Set A} : (matroid R A).IsBasis s t
 ↔ AlgebraicIndepOn R id s ∧ s subseteq t ∧ forall a in t, IsAlgebraic (adjoin R
 s) a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.eq_1`：∀ {α : Type u_1} (M : Matroid α) (I X : Set α), M.
IsBasis I X = (Maximal (fun A => M.Indep A ∧ A ⊆ X) I ∧ X ⊆ M.E)
· 使用定理 `Set.maximal_iff_forall_insert`：Set.maximal_iff_forall_insert (hP : foral
l ⦃s t⦄, P t -> s subseteq t -> P s) : Maximal P s ↔ P s ∧ forall x ∉ s, ¬ P (in
sert x s)
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `AlgebraicIndepOn.insert`：∀ {ι : Type u_1} {R : Type u_3} {A : Type v} {x
 : ι → A} [inst : CommRing R] [inst_1 : CommRing A]   [inst_2 : Algebra R A] {s 
: Set ι} {i :…
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicIndepOn.insert_iff`：AlgebraicIndepOn.insert_iff {s : Set ι} {i 
: ι} (h : i ∉ s) : AlgebraicIndepOn R x (insert i s) ↔ AlgebraicIndepOn R x s ∧ 
Transcendental (a…
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem matroid_isBasis_iff [IsDomain A] {s t : Set A} : (matroid R A).IsBasis s t ↔
    AlgebraicIndepOn R id s ∧ s ⊆ t ∧ ∀ a ∈ t, IsAlgebraic (adjoin R s) a := by
  rw [Matroid.IsBasis, maximal_iff_forall_insert fun s t h hst ↦ ⟨h.1.subset hst, hst.trans h.2⟩]
  simp_rw [matroid_indep_iff, ← and_assoc, matroid_e, subset_univ, and_true]
  exact and_congr_right fun h ↦ ⟨fun max a ha ↦ of_not_not fun tr ↦ max _
    (fun ha ↦ tr (isAlgebraic_algebraMap (⟨a, subset_adjoin ha⟩ : adjoin R s)))
      ⟨.insert h.1 (by rwa [image_id]), insert_subset ha h.2⟩,
    fun alg a ha h ↦ ((AlgebraicIndepOn.insert_iff ha).mp h.1).2 <| by
      rw [image_id]; exact alg _ <| h.2 <| mem_insert ..⟩

open Subsingleton in
/-
**AlgebraicIndependent.matroid_isBasis_iff_of_subsingleton** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicIndependent`。
形式化陈述：matroid_isBasis_iff_of_subsingleton [Subsingleton A] {s t : Set A} : (matr
oid R A).IsBasis s t ↔ s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用引理 `Subsingleton.to_noZeroDivisors`：Subsingleton.to_noZeroDivisors [Mul α] [
Zero α] [Subsingleton α] : NoZeroDivisors α where eq_zero_or_eq_zero_of_mul_eq_z
ero _
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem matroid_isBasis_iff_of_subsingleton [Subsingleton A] {s t : Set A} :
    (matroid R A).IsBasis s t ↔ s = t := by
  have := (FaithfulSMul.algebraMap_injective R A).subsingleton
  simp_rw [Matroid.IsBasis, matroid_indep_iff, of_subsingleton, true_and,
    matroid_e, subset_univ, and_true, maximal_le_iff]
/-
**AlgebraicIndependent.isAlgebraic_adjoin_iff_of_matroid_isBasis** 是 Mathlib 中的一
个定理，位于命名空间 `AlgebraicIndependent`。
形式化陈述：isAlgebraic_adjoin_iff_of_matroid_isBasis [NoZeroDivisors A] {s t : Set A}
 {a : A} (h : (matroid R A).IsBasis s t) : IsAlgebraic (adjoin R s) a ↔ IsAlgebr
aic (adjoin R t) a
参数：h : (matroid R A).IsBasis s t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `is_transcendental_of_subsingleton`：is_transcendental_of_subsingleton [Su
bsingleton R] (x : A) : Transcendental R x
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isDomain_iff_noZeroDivisors_and_nontrivial`：isDomain_iff_noZeroDivisors_
and_nontrivial [Ring α] : IsDomain α ↔ NoZeroDivisors α ∧ Nontrivial α
· 使用定理 `IsAlgebraic.adjoin_of_forall_isAlgebraic`：IsAlgebraic.adjoin_of_forall_i
sAlgebraic [NoZeroDivisors S] {s t : Set S} (alg : forall x in s \ t, IsAlgebrai
c (adjoin R t) x) {a : A} (ha …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `AlgebraicIndependent.matroid_isBasis_iff`：matroid_isBasis_iff [IsDomain 
A] {s t : Set A} : (matroid R A).IsBasis s t ↔ AlgebraicIndepOn R id s ∧ s subse
teq t ∧ forall a in t, IsAlgeb…
-/
theorem isAlgebraic_adjoin_iff_of_matroid_isBasis [NoZeroDivisors A] {s t : Set A} {a : A}
    (h : (matroid R A).IsBasis s t) : IsAlgebraic (adjoin R s) a ↔ IsAlgebraic (adjoin R t) a := by
  cases subsingleton_or_nontrivial A
  · apply iff_of_false <;> apply is_transcendental_of_subsingleton
  have := (isDomain_iff_noZeroDivisors_and_nontrivial A).mpr ⟨inferInstance, inferInstance⟩
  exact ⟨(·.adjoin_of_forall_isAlgebraic fun x hx ↦ (hx.2 <| h.1.1.2 hx.1).elim),
    (·.adjoin_of_forall_isAlgebraic fun x hx ↦ (matroid_isBasis_iff.mp h).2.2 _ hx.1)⟩
/-
**AlgebraicIndependent.matroid_closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicIn
dependent`。
形式化陈述：matroid_closure_eq [IsDomain A] {s : Set A} : (matroid R A).closure s = al
gebraicClosure (adjoin R s) A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X 
I : Set α}, M.IsBasis I X → M.closure I = M.closure X
· 使用定理 `Matroid.Indep.closure_eq_setOfPred_isBasis_insert`：∀ {α : Type u_2} {M :
 Matroid α} {I : Set α}, M.Indep I → M.closure I = {x | M.IsBasis I (insert x I)
}
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `AlgebraicIndependent.isAlgebraic_adjoin_iff_of_matroid_isBasis`：isAlgebr
aic_adjoin_iff_of_matroid_isBasis [NoZeroDivisors A] {s t : Set A} {a : A} (h : 
(matroid R A).IsBasis s t) : IsAlgebraic (adjoin R s…
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
theorem matroid_closure_eq [IsDomain A] {s : Set A} :
    (matroid R A).closure s = algebraicClosure (adjoin R s) A := by
  have ⟨B, hB⟩ := (matroid R A).exists_isBasis s
  simp_rw [← hB.closure_eq_closure, hB.1.1.1.closure_eq_setOfPred_isBasis_insert, Set.ext_iff,
    mem_ofPred, matroid_isBasis_iff, ← matroid_indep_iff, hB.1.1.1, subset_insert, true_and,
    SetLike.mem_coe, mem_algebraicClosure, ← isAlgebraic_adjoin_iff_of_matroid_isBasis hB,
    forall_mem_insert]
  exact fun _ ↦ and_iff_left fun x hx ↦ isAlgebraic_algebraMap (⟨x, subset_adjoin hx⟩ : adjoin R B)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicIndependent.matroid_isFlat_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicIn
dependent`。
形式化陈述：matroid_isFlat_iff [IsDomain A] {s : Set A} : (matroid R A).IsFlat s ↔ exi
sts S : Subalgebra R A, S = s ∧ forall a : A, IsAlgebraic S a -> a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isFlat_iff_closure_eq`：isFlat_iff_closure_eq : M.IsFlat F ↔ M.cl
osure F = F
· 使用定理 `AlgebraicIndependent.matroid_closure_eq`：matroid_closure_eq [IsDomain A]
 {s : Set A} : (matroid R A).closure s = algebraicClosure (adjoin R s) A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsAlgebraic.restrictScalars`：restrictScalars [Algebra.IsAlgebraic R S] {
a : A} (h : IsAlgebraic S a) : IsAlgebraic R a
· 使用定理 `instIsAlgebraicSubtypeMemSubalgebraAlgebraicClosure`：∀ (R : Type u_1) (S
 : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [i
nst_3 : IsDomain R],   Algebra.IsAlgebrai…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Algebra.adjoin_eq`：adjoin_eq (S : Subalgebra R A) : adjoin R ↑S = S
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
theorem matroid_isFlat_iff [IsDomain A] {s : Set A} :
    (matroid R A).IsFlat s ↔ ∃ S : Subalgebra R A, S = s ∧ ∀ a : A, IsAlgebraic S a → a ∈ s := by
  rw [Matroid.isFlat_iff_closure_eq, matroid_closure_eq]
  set S := algebraicClosure (adjoin R s) A
  refine ⟨fun eq ↦ ⟨S.restrictScalars R, eq, fun a (h : IsAlgebraic S _) ↦ ?_⟩, ?_⟩
  · rw [← eq]; exact h.restrictScalars (adjoin R s)
  rintro ⟨s, rfl, hs⟩
  refine Set.ext fun a ↦ ⟨(hs _ <| adjoin_eq s ▸ ·), fun h ↦ ?_⟩
  exact isAlgebraic_algebraMap (A := A) (by exact (⟨a, subset_adjoin h⟩ : adjoin R s))
/-
**AlgebraicIndependent.matroid_spanning_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Independent`。
形式化陈述：matroid_spanning_iff [IsDomain A] {s : Set A} : (matroid R A).Spanning s ↔
 Algebra.IsAlgebraic (adjoin R s) A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `AlgebraicIndependent.matroid_closure_eq`：matroid_closure_eq [IsDomain A]
 {s : Set A} : (matroid R A).closure s = algebraicClosure (adjoin R s) A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem matroid_spanning_iff [IsDomain A] {s : Set A} :
    (matroid R A).Spanning s ↔ Algebra.IsAlgebraic (adjoin R s) A := by
  simp_rw [Matroid.spanning_iff, matroid_e, subset_univ, and_true, eq_univ_iff_forall,
    matroid_closure_eq, SetLike.mem_coe, mem_algebraicClosure, Algebra.isAlgebraic_def]

open Subsingleton -- brings the Subsingleton.to_noZeroDivisors instance into scope
/-
**AlgebraicIndependent.matroid_isFlat_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicIndependent`。
形式化陈述：matroid_isFlat_of_subsingleton [Subsingleton A] (s : Set A) : (matroid R A
).IsFlat s
参数：s : Set A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subsingleton.to_noZeroDivisors`：Subsingleton.to_noZeroDivisors [Mul α] [
Zero α] [Subsingleton α] : NoZeroDivisors α where eq_zero_or_eq_zero_of_mul_eq_z
ero _
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem matroid_isFlat_of_subsingleton [Subsingleton A] (s : Set A) : (matroid R A).IsFlat s := by
  simp_rw [Matroid.isFlat_iff, matroid_e, subset_univ,
    and_true, matroid_isBasis_iff_of_subsingleton]
  exact fun I X hIs hIX ↦ (hIX.symm.trans hIs).subset
/-
**AlgebraicIndependent.matroid_closure_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicIndependent`。
形式化陈述：matroid_closure_of_subsingleton [Subsingleton A] (s : Set A) : (matroid R 
A).closure s = s
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subsingleton.to_noZeroDivisors`：Subsingleton.to_noZeroDivisors [Mul α] [
Zero α] [Subsingleton α] : NoZeroDivisors α where eq_zero_or_eq_zero_of_mul_eq_z
ero _
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
· 使用定理 `subset_refl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] (a : α), a ⊆ a
· 使用定理 `Set.subset_sInter`：subset_sInter {S : Set (Set α)} {t : Set α} (h : fora
ll t' in S, t subseteq t') : t subseteq ⋂₀ S
-/
theorem matroid_closure_of_subsingleton [Subsingleton A] (s : Set A) :
    (matroid R A).closure s = s := by
  simp_rw [Matroid.closure, matroid_isFlat_of_subsingleton, true_and, matroid_e, inter_univ]
  exact subset_antisymm (sInter_subset_of_mem <| subset_refl s) (subset_sInter fun _ ↦ id)
/-
**AlgebraicIndependent.matroid_spanning_iff_of_subsingleton** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicIndependent`。
形式化陈述：matroid_spanning_iff_of_subsingleton [Subsingleton A] {s : Set A} : (matro
id R A).Spanning s ↔ s = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subsingleton.to_noZeroDivisors`：Subsingleton.to_noZeroDivisors [Mul α] [
Zero α] [Subsingleton α] : NoZeroDivisors α where eq_zero_or_eq_zero_of_mul_eq_z
ero _
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicIndependent.matroid_closure_of_subsingleton`：matroid_closure_of
_subsingleton [Subsingleton A] (s : Set A) : (matroid R A).closure s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem matroid_spanning_iff_of_subsingleton [Subsingleton A] {s : Set A} :
    (matroid R A).Spanning s ↔ s = univ := by
  simp_rw [Matroid.spanning_iff, matroid_closure_of_subsingleton, matroid_e, subset_univ, and_true]

end AlgebraicIndependent

/-- If `s ⊆ t` are subsets in an `R`-algebra `A` such that `s` is algebraically independent over
`R`, and `A` is algebraic over the `R`-algebra generated by `t`, then there is a transcendence
basis of `A` over `R` between `s` and `t`, provided that `A` is a domain.

This may fail if only `R` is assumed to be a domain but `A` is not, because of failure of
transitivity of algebraicity: there may exist `a : A` such that `S := R[a]` is algebraic over
`R` and `A` is algebraic over `S`, but `A` nonetheless contains a transcendental element over `R`.
The only `R`-algebraically independent subset of `{a}` is `∅`, which is not a transcendence basis.
See the docstring of `IsAlgebraic.restrictScalars_of_isIntegral` for an example. -/
/-
**exists_isTranscendenceBasis_between** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isTranscendenceBasis_between [NoZeroDivisors A] (s t : Set A) (hst 
: s subseteq t) (hs : AlgebraicIndepOn R id s) [ht : Algebra.IsAlgebraic (adjoin
 R t) A] : exists u, s subseteq u ∧ u subseteq t ∧ IsTranscendenceBasis R ((↑) :
 u -> A)
参数：s t : Set A；hst : s subseteq t；hs : AlgebraicIndepOn R id s；adjoin R t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.nontrivial`：Algebra.IsAlgebraic.nontrivial [alg : Al
gebra.IsAlgebraic R A] : Nontrivial R
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isDomain_iff_noZeroDivisors_and_nontrivial`：isDomain_iff_noZeroDivisors_
and_nontrivial [Ring α] : IsDomain α ↔ NoZeroDivisors α ∧ Nontrivial α
· 使用引理 `faithfulSMul_iff_algebraMap_injective`：faithfulSMul_iff_algebraMap_injec
tive : FaithfulSMul R A ↔ Injective (algebraMap R A)
· 使用定理 `AlgebraicIndependent.algebraMap_injective`：algebraMap_injective : Inject
ive (algebraMap R A)
· 使用定理 `Matroid.Indep.exists_isBase_subset_spanning`：∀ {α : Type u_2} {M : Matro
id α} {S I : Set α}, M.Indep I → M.Spanning S → I ⊆ S → ∃ B, M.IsBase B ∧ I ⊆ B 
∧ B ⊆ S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicIndependent.matroid_indep_iff`：matroid_indep_iff {s : Set A} : 
(matroid R A).Indep s ↔ AlgebraicIndepOn R id s
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `AlgebraicIndependent.matroid_spanning_iff`：matroid_spanning_iff [IsDomai
n A] {s : Set A} : (matroid R A).Spanning s ↔ Algebra.IsAlgebraic (adjoin R s) A

--- 原说明 ---
If `s ⊆ t` are subsets in an `R`-algebra `A` such that `s` is algebraically inde
pendent over
`R`, and `A` is algebraic over the `R`-algebra generated by `t`, then there is a
 transcendence
basis of `A` over `R` between `s` and `t`, provided that `A` is a domain.

This may fail if only `R` is assumed to be a domain but `A` is not, because of f
ailure of
transitivity of algebraicity: there may exist `a : A` such that `S := R[a]` is a
lgebraic over
`R` and `A` is algebraic over `S`, but `A` nonetheless contains a transcendental
 element over `R`.
The only `R`-algebraically independent subset of `{a}` is `∅`, which is not a tr
anscendence basis.
See the docstring of `IsAlgebraic.restrictScalars_of_isIntegral` for an example.
-/
theorem exists_isTranscendenceBasis_between [NoZeroDivisors A] (s t : Set A) (hst : s ⊆ t)
    (hs : AlgebraicIndepOn R id s) [ht : Algebra.IsAlgebraic (adjoin R t) A] :
    ∃ u, s ⊆ u ∧ u ⊆ t ∧ IsTranscendenceBasis R ((↑) : u → A) := by
  have := ht.nontrivial
  have := Subtype.val_injective (p := (· ∈ adjoin R t)).nontrivial
  have := (isDomain_iff_noZeroDivisors_and_nontrivial A).mpr ⟨inferInstance, inferInstance⟩
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr hs.algebraMap_injective
  rw [← matroid_spanning_iff] at ht
  rw [← matroid_indep_iff] at hs
  have ⟨B, base, hsB, hBt⟩ := hs.exists_isBase_subset_spanning ht hst
  exact ⟨B, hsB, hBt, base⟩
/-
**exists_isTranscendenceBasis_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isTranscendenceBasis_subset [NoZeroDivisors A] [FaithfulSMul R A] (
s : Set A) [Algebra.IsAlgebraic (adjoin R s) A] : exists t, t subseteq s ∧ IsTra
nscendenceBasis R ((↑) : t -> A)
参数：s : Set A；adjoin R s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_isTranscendenceBasis_between`：exists_isTranscendenceBasis_between
 [NoZeroDivisors A] (s t : Set A) (hst : s subseteq t) (hs : AlgebraicIndepOn R 
id s) [ht : Algebra.IsAlg…
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `algebraicIndependent_empty_iff`：algebraicIndependent_empty_iff : Algebra
icIndependent R ((↑) : (∅ : Set A) -> A) ↔ Injective (algebraMap R A)
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
theorem exists_isTranscendenceBasis_subset [NoZeroDivisors A] [FaithfulSMul R A]
    (s : Set A) [Algebra.IsAlgebraic (adjoin R s) A] :
    ∃ t, t ⊆ s ∧ IsTranscendenceBasis R ((↑) : t → A) := by
  have ⟨t, _, ht⟩ := exists_isTranscendenceBasis_between ∅ s (empty_subset _)
    ((algebraicIndependent_empty_iff ..).mpr <| FaithfulSMul.algebraMap_injective R A)
  exact ⟨t, ht⟩
/-
**isAlgebraic_iff_exists_isTranscendenceBasis_subset** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：isAlgebraic_iff_exists_isTranscendenceBasis_subset [IsDomain A] [FaithfulS
Mul R A] {s : Set A} : Algebra.IsAlgebraic (adjoin R s) A ↔ exists t, t subseteq
 s ∧ IsTranscendenceBasis R ((↑) : t -> A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用引理 `Matroid.spanning_iff_exists_isBase_subset`：spanning_iff_exists_isBase_su
bset (hS : S subseteq M.E
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem isAlgebraic_iff_exists_isTranscendenceBasis_subset
    [IsDomain A] [FaithfulSMul R A] {s : Set A} :
    Algebra.IsAlgebraic (adjoin R s) A ↔ ∃ t, t ⊆ s ∧ IsTranscendenceBasis R ((↑) : t → A) := by
  simp_rw [← matroid_spanning_iff, ← matroid_isBase_iff, and_comm (a := _ ⊆ s)]
  exact Matroid.spanning_iff_exists_isBase_subset (subset_univ _)

open Cardinal AlgebraicIndependent

namespace IsTranscendenceBasis

variable [Nontrivial R] [NoZeroDivisors A]

/-- Any transcendence basis of a domain has cardinality equal to transcendental degree. -/
/-
**IsTranscendenceBasis.lift_cardinalMk_eq_trdeg** 是 Mathlib 中的一个定理，位于命名空间 `IsTra
nscendenceBasis`。
形式化陈述：lift_cardinalMk_eq_trdeg (hx : IsTranscendenceBasis R x) : lift.{w} #ι = l
ift.{u} (trdeg R A)
参数：hx : IsTranscendenceBasis R x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `faithfulSMul_iff_algebraMap_injective`：faithfulSMul_iff_algebraMap_injec
tive : FaithfulSMul R A ↔ Injective (algebraMap R A)
· 使用定理 `AlgebraicIndependent.algebraMap_injective`：algebraMap_injective : Inject
ive (algebraMap R A)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicIndependent.matroid_cRank_eq`：matroid_cRank_eq : (matroid R A).
cRank = trdeg R A
· 使用定理 `Matroid.IsBase.cardinalMk_eq_cRank`：∀ {α : Type u} {M : Matroid α} {B : 
Set α} [M.InvariantCardinalRank], M.IsBase B → Cardinal.mk ↑B = M.cRank
· 使用定理 `AlgebraicIndependent.instFinitaryMatroid`：∀ (R : Type u_1) (A : Type w) 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [inst_3 : Fai
thfulSMul R A] [inst_4 : NoZer…
· 使用定理 `AlgebraicIndependent.matroid_isBase_iff`：matroid_isBase_iff {s : Set A} 
: (matroid R A).IsBase s ↔ IsTranscendenceBasis R ((↑) : s -> A)
· 使用定理 `IsTranscendenceBasis.to_subtype_range`：IsTranscendenceBasis.to_subtype_r
ange (hx : IsTranscendenceBasis R x) : IsTranscendenceBasis R ((↑) : range x -> 
A)
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `AlgebraicIndependent.injective`：∀ {ι : Type u} {R : Type u_2} {A : Type 
v} {x : ι → A} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],
   AlgebraicIndepend…

--- 原说明 ---
Any transcendence basis of a domain has cardinality equal to transcendental degr
ee.
-/
theorem lift_cardinalMk_eq_trdeg (hx : IsTranscendenceBasis R x) :
    lift.{w} #ι = lift.{u} (trdeg R A) := by
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr hx.1.algebraMap_injective
  rw [← matroid_cRank_eq, ← (matroid_isBase_iff.mpr hx.to_subtype_range).cardinalMk_eq_cRank,
    lift_mk_eq'.mpr ⟨.ofInjective _ hx.1.injective⟩]
/-
**IsTranscendenceBasis.cardinalMk_eq_trdeg** 是 Mathlib 中的一个定理，位于命名空间 `IsTranscen
denceBasis`。
形式化陈述：cardinalMk_eq_trdeg {ι : Type w} {x : ι -> A} (hx : IsTranscendenceBasis R
 x) : #ι = trdeg R A
参数：hx : IsTranscendenceBasis R x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `IsTranscendenceBasis.lift_cardinalMk_eq_trdeg`：lift_cardinalMk_eq_trdeg 
(hx : IsTranscendenceBasis R x) : lift.{w} #ι = lift.{u} (trdeg R A)
-/
theorem cardinalMk_eq_trdeg {ι : Type w} {x : ι → A} (hx : IsTranscendenceBasis R x) :
    #ι = trdeg R A := by
  rw [← lift_id #ι, lift_cardinalMk_eq_trdeg hx, lift_id]

/-- Any two transcendence bases of a domain `A` have the same cardinality.
May fail if `A` is not a domain; see https://mathoverflow.net/a/144580. -/
@[stacks 030F]
/-
**IsTranscendenceBasis.lift_cardinalMk_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsTranscend
enceBasis`。
形式化陈述：lift_cardinalMk_eq (hx : IsTranscendenceBasis R x) (hy : IsTranscendenceBa
sis R y) : lift.{u'} #ι = lift.{u} #ι'
参数：hx : IsTranscendenceBasis R x；hy : IsTranscendenceBasis R y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `IsTranscendenceBasis.lift_cardinalMk_eq_trdeg`：lift_cardinalMk_eq_trdeg 
(hx : IsTranscendenceBasis R x) : lift.{w} #ι = lift.{u} (trdeg R A)

--- 原说明 ---
Any two transcendence bases of a domain `A` have the same cardinality.
May fail if `A` is not a domain; see https://mathoverflow.net/a/144580.
-/
theorem lift_cardinalMk_eq (hx : IsTranscendenceBasis R x) (hy : IsTranscendenceBasis R y) :
    lift.{u'} #ι = lift.{u} #ι' := by
  rw [← lift_inj.{_, w}, lift_lift, lift_lift, ← lift_lift.{w, u'}, hx.lift_cardinalMk_eq_trdeg,
    ← lift_lift.{w, u}, hy.lift_cardinalMk_eq_trdeg, lift_lift, lift_lift]
/-
**IsTranscendenceBasis.cardinalMk_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsTranscendenceB
asis`。
形式化陈述：∀ {ι : Type u} {R : Type u_1} {A : Type w} {x : ι → A} [inst : CommRing R]
 [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Nontrivial R] [NoZeroDivisors A
] {ι' : Type u} {y : ι' → A},   IsTranscendenceBasis R x → IsTranscendenceBasis 
R y → Cardinal.mk ι = Cardinal.mk ι'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `IsTranscendenceBasis.lift_cardinalMk_eq`：lift_cardinalMk_eq (hx : IsTran
scendenceBasis R x) (hy : IsTranscendenceBasis R y) : lift.{u'} #ι = lift.{u} #ι
'
-/
@[stacks 030F] theorem cardinalMk_eq {ι' : Type u} {y : ι' → A}
    (hx : IsTranscendenceBasis R x) (hy : IsTranscendenceBasis R y) :
    #ι = #ι' := by
  rw [← lift_id #ι, lift_cardinalMk_eq hx hy, lift_id]

end IsTranscendenceBasis

-- TODO: generalize to Nontrivial S
@[simp]
/-
**MvPolynomial.trdeg_of_isDomain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MvPolynomial.trdeg_of_isDomain [IsDomain S] : trdeg S (MvPolynomial ι S) =
 lift.{v} #ι
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsTranscendenceBasis.lift_cardinalMk_eq_trdeg`：lift_cardinalMk_eq_trdeg 
(hx : IsTranscendenceBasis R x) : lift.{w} #ι = lift.{u} (trdeg R A)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `MvPolynomial.instNoZeroDivisors`：∀ {R : Type u} {σ : Type u_1} [inst : C
ommSemiring R] [NoZeroDivisors R], NoZeroDivisors (MvPolynomial σ R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsTranscendenceBasis.mvPolynomial`：IsTranscendenceBasis.mvPolynomial [No
ntrivial R] : IsTranscendenceBasis R (X (R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
-/
theorem MvPolynomial.trdeg_of_isDomain [IsDomain S] : trdeg S (MvPolynomial ι S) = lift.{v} #ι := by
  have := (IsTranscendenceBasis.mvPolynomial ι S).lift_cardinalMk_eq_trdeg.symm
  rwa [lift_id', ← lift_lift.{u}, lift_id] at this

-- TODO: generalize to Nontrivial R
@[simp]
/-
**Polynomial.trdeg_of_isDomain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.trdeg_of_isDomain [IsDomain R] : trdeg R (Polynomial R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsTranscendenceBasis.lift_cardinalMk_eq_trdeg`：lift_cardinalMk_eq_trdeg 
(hx : IsTranscendenceBasis R x) : lift.{w} #ι = lift.{u} (trdeg R A)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsTranscendenceBasis.polynomial`：IsTranscendenceBasis.polynomial [Nonemp
ty ι] [Subsingleton ι] : IsTranscendenceBasis R fun _ : ι => (.X : Polynomial R)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
-/
theorem Polynomial.trdeg_of_isDomain [IsDomain R] : trdeg R (Polynomial R) = 1 := by
  simpa using (IsTranscendenceBasis.polynomial Unit R).lift_cardinalMk_eq_trdeg.symm

-- TODO: generalize to Nontrivial S
/-
**trdeg_lt_aleph0_of_finiteType** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trdeg_lt_aleph0_of_finiteType [IsDomain R] [fin : FiniteType R S] : trdeg 
R S < ℵ₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.FiniteType.iff_quotient_mvPolynomial''`：iff_quotient_mvPolynomia
l'' : FiniteType R S ↔ exists (n : Nat) (f : MvPolynomial (Fin n) R ->ₐ[R] S), S
urjective f
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `lift_trdeg_le_of_surjective`：lift_trdeg_le_of_surjective (f : A ->ₐ[R] A
') (hf : Surjective f) : lift.{v} (trdeg R A') <= lift.{v'} (trdeg R A)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.trdeg_of_isDomain`：MvPolynomial.trdeg_of_isDomain [IsDomain
 S] : trdeg S (MvPolynomial ι S) = lift.{v} #ι
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
-/
theorem trdeg_lt_aleph0_of_finiteType [IsDomain R] [fin : FiniteType R S] : trdeg R S < ℵ₀ :=
  have ⟨n, f, surj⟩ := FiniteType.iff_quotient_mvPolynomial''.mp fin
  lift_lt.mp <| (lift_trdeg_le_of_surjective f surj).trans_lt <| by simp

namespace Algebra.IsAlgebraic

variable (R x) (s : Set A)

variable [NoZeroDivisors A]

/-
**Algebra.IsAlgebraic.isDomain_of_adjoin_range** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a.IsAlgebraic`。
形式化陈述：isDomain_of_adjoin_range [Algebra.IsAlgebraic (adjoin R s) A] : IsDomain A
参数：adjoin R s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.nontrivial`：Algebra.IsAlgebraic.nontrivial [alg : Al
gebra.IsAlgebraic R A] : Nontrivial R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isDomain_iff_noZeroDivisors_and_nontrivial`：isDomain_iff_noZeroDivisors_
and_nontrivial [Ring α] : IsDomain α ↔ NoZeroDivisors α ∧ Nontrivial α
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma isDomain_of_adjoin_range [Algebra.IsAlgebraic (adjoin R s) A] : IsDomain A :=
  have := Algebra.IsAlgebraic.nontrivial (adjoin R s) A
  (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr
    ⟨‹_›, (Subtype.val_injective (p := (· ∈ adjoin R s))).nontrivial⟩
/-
**Algebra.IsAlgebraic.trdeg_le_cardinalMk** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsA
lgebraic`。
形式化陈述：trdeg_le_cardinalMk [alg : Algebra.IsAlgebraic (adjoin R s) A] : trdeg R A
 <= #s
参数：adjoin R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.IsAlgebraic.isDomain_of_adjoin_range`：isDomain_of_adjoin_range [
Algebra.IsAlgebraic (adjoin R s) A] : IsDomain A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `faithfulSMul_iff_algebraMap_injective`：faithfulSMul_iff_algebraMap_injec
tive : FaithfulSMul R A ↔ Injective (algebraMap R A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicIndependent.matroid_cRank_eq`：matroid_cRank_eq : (matroid R A).
cRank = trdeg R A
· 使用定理 `Matroid.Spanning.cRank_le_cardinalMk`：∀ {α : Type u} {M : Matroid α} {X 
: Set α} [M.InvariantCardinalRank], M.Spanning X → M.cRank ≤ Cardinal.mk ↑X
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `AlgebraicIndependent.instFinitaryMatroid`：∀ (R : Type u_1) (A : Type w) 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [inst_3 : Fai
thfulSMul R A] [inst_4 : NoZer…
· 使用定理 `AlgebraicIndependent.matroid_spanning_iff`：matroid_spanning_iff [IsDomai
n A] {s : Set A} : (matroid R A).Spanning s ↔ Algebra.IsAlgebraic (adjoin R s) A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `trdeg_eq_zero_of_not_injective`：trdeg_eq_zero_of_not_injective (h : ¬ In
jective (algebraMap R A)) : trdeg R A = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem trdeg_le_cardinalMk [alg : Algebra.IsAlgebraic (adjoin R s) A] : trdeg R A ≤ #s := by
  by_cases h : Injective (algebraMap R A)
  on_goal 2 => simp [trdeg_eq_zero_of_not_injective h]
  have := isDomain_of_adjoin_range R s
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr h
  rw [← matroid_spanning_iff, ← matroid_cRank_eq] at *
  exact alg.cRank_le_cardinalMk

variable [FaithfulSMul R A]
/-
**Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite** 是 Mathli
b 中的一个定理，位于命名空间 `Algebra.IsAlgebraic`。
形式化陈述：isTranscendenceBasis_of_lift_le_trdeg_of_finite [Finite ι] [alg : Algebra.
IsAlgebraic (adjoin R (range x)) A] (le : lift.{w} #ι <= lift.{u} (trdeg R A)) :
 IsTranscendenceBasis R x
参数：adjoin R (range x)；le : lift.{w} #ι <= lift.{u} (trdeg R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Algebra.IsAlgebraic.trdeg_le_cardinalMk`：trdeg_le_cardinalMk [alg : Alge
bra.IsAlgebraic (adjoin R s) A] : trdeg R A <= #s
· 使用定理 `Function.Surjective.bijective_of_nat_card_le`：∀ {α : Type u_1} {β : Type
 u_2} [Finite α] {f : α → β},   Function.Surjective f → Nat.card α ≤ Nat.card β 
→ Function.Bijective f
· 使用定理 `Set.rangeFactorization_surjective`：∀ {α : Type u} {ι : Sort u_1} {f : ι 
→ α}, Function.Surjective (Set.rangeFactorization f)
· 使用引理 `Nat.card_le_card_of_injective`：card_le_card_of_injective {α : Type u} {β
 : Type v} [Finite β] (f : α -> β) (hf : Injective f) : Nat.card α <= Nat.card β
· 使用定理 `IsTranscendenceBasis.of_subtype_range`：∀ {R : Type u_3} {A : Type u_5} [
inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {ι : Type u_7}  
 {f : ι → A}, Function.Inje…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `Algebra.IsAlgebraic.isDomain_of_adjoin_range`：isDomain_of_adjoin_range [
Algebra.IsAlgebraic (adjoin R s) A] : IsDomain A
· 使用定理 `Matroid.Spanning.isBase_of_le_cRank_of_finite`：∀ {α : Type u} {M : Matro
id α} {X : Set α}, M.Spanning X → Cardinal.mk ↑X ≤ M.cRank → X.Finite → M.IsBase
 X
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicIndependent.matroid_spanning_iff`：matroid_spanning_iff [IsDomai
n A] {s : Set A} : (matroid R A).Spanning s ↔ Algebra.IsAlgebraic (adjoin R s) A
· 使用定理 `Cardinal.mk_range_le_lift`：mk_range_le_lift {α : Type u} {β : Type v} {f
 : α -> β} : lift.{u} #(range f) <= lift.{v} #α
· 使用定理 `AlgebraicIndependent.matroid_cRank_eq`：matroid_cRank_eq : (matroid R A).
cRank = trdeg R A
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
-/
theorem isTranscendenceBasis_of_lift_le_trdeg_of_finite
    [Finite ι] [alg : Algebra.IsAlgebraic (adjoin R (range x)) A]
    (le : lift.{w} #ι ≤ lift.{u} (trdeg R A)) : IsTranscendenceBasis R x := by
  have ⟨_, h⟩ := lift_mk_le'.mp (le.trans <| lift_le.mpr <| trdeg_le_cardinalMk R (range x))
  have := rangeFactorization_surjective.bijective_of_nat_card_le (Nat.card_le_card_of_injective _ h)
  refine .of_subtype_range (fun _ _ ↦ (this.1 <| Subtype.ext ·)) ?_
  have := isDomain_of_adjoin_range R (range x)
  rw [← matroid_spanning_iff, ← matroid_cRank_eq] at *
  exact alg.isBase_of_le_cRank_of_finite (lift_le.mp <| mk_range_le_lift.trans le) (finite_range x)
/-
**Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite** 是 Mathlib 中的一
个定理，位于命名空间 `Algebra.IsAlgebraic`。
形式化陈述：isTranscendenceBasis_of_le_trdeg_of_finite {ι : Type w} [Finite ι] (x : ι 
-> A) [Algebra.IsAlgebraic (adjoin R (range x)) A] (le : #ι <= trdeg R A) : IsTr
anscendenceBasis R x
参数：x : ι -> A；adjoin R (range x)；le : #ι <= trdeg R A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite`：isT
ranscendenceBasis_of_lift_le_trdeg_of_finite [Finite ι] [alg : Algebra.IsAlgebra
ic (adjoin R (range x)) A] (le : lift.{w} #ι <= lift.{u} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem isTranscendenceBasis_of_le_trdeg_of_finite {ι : Type w} [Finite ι] (x : ι → A)
    [Algebra.IsAlgebraic (adjoin R (range x)) A] (le : #ι ≤ trdeg R A) :
    IsTranscendenceBasis R x :=
  isTranscendenceBasis_of_lift_le_trdeg_of_finite R x (by rwa [lift_id, lift_id])
/-
**Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg** 是 Mathlib 中的一个定理，位
于命名空间 `Algebra.IsAlgebraic`。
形式化陈述：isTranscendenceBasis_of_lift_le_trdeg [Algebra.IsAlgebraic (adjoin R (rang
e x)) A] (fin : trdeg R A < ℵ₀) (le : lift.{w} #ι <= lift.{u} (trdeg R A)) : IsT
ranscendenceBasis R x
参数：adjoin R (range x)；fin : trdeg R A < ℵ₀；le : lift.{w} #ι <= lift.{u} (trdeg R
 A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Cardinal.mk_lt_aleph0_iff`：mk_lt_aleph0_iff : #α < ℵ₀ ↔ Finite α
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite`：isT
ranscendenceBasis_of_lift_le_trdeg_of_finite [Finite ι] [alg : Algebra.IsAlgebra
ic (adjoin R (range x)) A] (le : lift.{w} #ι <= lift.{u} …
-/
theorem isTranscendenceBasis_of_lift_le_trdeg [Algebra.IsAlgebraic (adjoin R (range x)) A]
    (fin : trdeg R A < ℵ₀) (le : lift.{w} #ι ≤ lift.{u} (trdeg R A)) :
    IsTranscendenceBasis R x :=
  have := mk_lt_aleph0_iff.mp (lift_lt.mp <| le.trans_lt <| (lift_lt.mpr fin).trans_eq <| by simp)
  isTranscendenceBasis_of_lift_le_trdeg_of_finite R x le
/-
**Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg** 是 Mathlib 中的一个定理，位于命名空间
 `Algebra.IsAlgebraic`。
形式化陈述：isTranscendenceBasis_of_le_trdeg {ι : Type w} (x : ι -> A) [Algebra.IsAlge
braic (adjoin R (range x)) A] (fin : trdeg R A < ℵ₀) (le : #ι <= trdeg R A) : Is
TranscendenceBasis R x
参数：x : ι -> A；adjoin R (range x)；fin : trdeg R A < ℵ₀；le : #ι <= trdeg R A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg`：isTranscenden
ceBasis_of_lift_le_trdeg [Algebra.IsAlgebraic (adjoin R (range x)) A] (fin : trd
eg R A < ℵ₀) (le : lift.{w} #ι <= lift.{u} (trd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem isTranscendenceBasis_of_le_trdeg {ι : Type w} (x : ι → A)
    [Algebra.IsAlgebraic (adjoin R (range x)) A] (fin : trdeg R A < ℵ₀)
    (le : #ι ≤ trdeg R A) : IsTranscendenceBasis R x :=
  isTranscendenceBasis_of_lift_le_trdeg R x fin (by rwa [lift_id, lift_id])

end Algebra.IsAlgebraic

namespace AlgebraicIndependent

variable [Nontrivial R] [NoZeroDivisors A]

/-
**AlgebraicIndependent.isTranscendenceBasis_of_lift_trdeg_le** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicIndependent`。
形式化陈述：isTranscendenceBasis_of_lift_trdeg_le (hx : AlgebraicIndependent R x) (fin
 : trdeg R A < ℵ₀) (le : lift.{u} (trdeg R A) <= lift.{w} #ι) : IsTranscendenceB
asis R x
参数：hx : AlgebraicIndependent R x；fin : trdeg R A < ℵ₀；le : lift.{u} (trdeg R A) 
<= lift.{w} #ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `faithfulSMul_iff_algebraMap_injective`：faithfulSMul_iff_algebraMap_injec
tive : FaithfulSMul R A ↔ Injective (algebraMap R A)
· 使用定理 `AlgebraicIndependent.algebraMap_injective`：algebraMap_injective : Inject
ive (algebraMap R A)
· 使用定理 `IsTranscendenceBasis.of_subtype_range`：∀ {R : Type u_3} {A : Type u_5} [
inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {ι : Type u_7}  
 {f : ι → A}, Function.Inje…
· 使用定理 `AlgebraicIndependent.injective`：∀ {ι : Type u} {R : Type u_2} {A : Type 
v} {x : ι → A} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],
   AlgebraicIndepend…
· 使用定理 `Matroid.Indep.isBase_of_cRank_le`：∀ {α : Type u} {M : Matroid α} {I : Se
t α} [M.RankFinite], M.Indep I → M.cRank ≤ Cardinal.mk ↑I → M.IsBase I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.rankFinite_iff_cRank_lt_aleph0`：rankFinite_iff_cRank_lt_aleph0 :
 M.RankFinite ↔ M.cRank < ℵ₀
· 使用定理 `AlgebraicIndependent.matroid_cRank_eq`：matroid_cRank_eq : (matroid R A).
cRank = trdeg R A
· 使用定理 `AlgebraicIndependent.matroid_indep_iff`：matroid_indep_iff {s : Set A} : 
(matroid R A).Indep s ↔ AlgebraicIndepOn R id s
· 使用定理 `AlgebraicIndependent.to_subtype_range`：AlgebraicIndependent.to_subtype_r
ange (hx : AlgebraicIndependent R x) : AlgebraicIndependent R ((↑) : range x -> 
A)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Cardinal.mk_range_eq_of_injective`：mk_range_eq_of_injective {α : Type u}
 {β : Type v} {f : α -> β} (hf : Injective f) : lift.{u} #(range f) = lift.{v} #
α
-/
theorem isTranscendenceBasis_of_lift_trdeg_le (hx : AlgebraicIndependent R x)
    (fin : trdeg R A < ℵ₀) (le : lift.{u} (trdeg R A) ≤ lift.{w} #ι) :
    IsTranscendenceBasis R x := by
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr hx.algebraMap_injective
  rw [← matroid_cRank_eq, ← Matroid.rankFinite_iff_cRank_lt_aleph0] at fin
  exact .of_subtype_range hx.injective <| matroid_indep_iff.mpr hx.to_subtype_range
    |>.isBase_of_cRank_le <| lift_le.mp <| (matroid_cRank_eq R A ▸ le).trans_eq
      (mk_range_eq_of_injective hx.injective).symm
/-
**AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicIndependent`。
形式化陈述：isTranscendenceBasis_of_trdeg_le {ι : Type w} {x : ι -> A} (hx : Algebraic
Independent R x) (fin : trdeg R A < ℵ₀) (le : trdeg R A <= #ι) : IsTranscendence
Basis R x
参数：hx : AlgebraicIndependent R x；fin : trdeg R A < ℵ₀；le : trdeg R A <= #ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.isTranscendenceBasis_of_lift_trdeg_le`：isTranscende
nceBasis_of_lift_trdeg_le (hx : AlgebraicIndependent R x) (fin : trdeg R A < ℵ₀)
 (le : lift.{u} (trdeg R A) <= lift.{w} #ι) : Is…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem isTranscendenceBasis_of_trdeg_le {ι : Type w} {x : ι → A} (hx : AlgebraicIndependent R x)
    (fin : trdeg R A < ℵ₀) (le : trdeg R A ≤ #ι) : IsTranscendenceBasis R x :=
  isTranscendenceBasis_of_lift_trdeg_le hx fin (by rwa [lift_id, lift_id])
/-
**AlgebraicIndependent.isTranscendenceBasis_of_lift_trdeg_le_of_finite** 是 Mathl
ib 中的一个定理，位于命名空间 `AlgebraicIndependent`。
形式化陈述：isTranscendenceBasis_of_lift_trdeg_le_of_finite [Finite ι] (hx : Algebraic
Independent R x) (le : lift.{u} (trdeg R A) <= lift.{w} #ι) : IsTranscendenceBas
is R x
参数：hx : AlgebraicIndependent R x；le : lift.{u} (trdeg R A) <= lift.{w} #ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.isTranscendenceBasis_of_lift_trdeg_le`：isTranscende
nceBasis_of_lift_trdeg_le (hx : AlgebraicIndependent R x) (fin : trdeg R A < ℵ₀)
 (le : lift.{u} (trdeg R A) <= lift.{w} #ι) : Is…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
-/
theorem isTranscendenceBasis_of_lift_trdeg_le_of_finite [Finite ι] (hx : AlgebraicIndependent R x)
    (le : lift.{u} (trdeg R A) ≤ lift.{w} #ι) : IsTranscendenceBasis R x :=
  isTranscendenceBasis_of_lift_trdeg_le hx
    (lift_lt.mp <| le.trans_lt <| by simp) le
/-
**AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicIndependent`。
形式化陈述：isTranscendenceBasis_of_trdeg_le_of_finite {ι : Type w} [Finite ι] {x : ι 
-> A} (hx : AlgebraicIndependent R x) (le : trdeg R A <= #ι) : IsTranscendenceBa
sis R x
参数：hx : AlgebraicIndependent R x；le : trdeg R A <= #ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.isTranscendenceBasis_of_lift_trdeg_le_of_finite`：is
TranscendenceBasis_of_lift_trdeg_le_of_finite [Finite ι] (hx : AlgebraicIndepend
ent R x) (le : lift.{u} (trdeg R A) <= lift.{w} #ι) : IsTr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem isTranscendenceBasis_of_trdeg_le_of_finite {ι : Type w} [Finite ι] {x : ι → A}
    (hx : AlgebraicIndependent R x) (le : trdeg R A ≤ #ι) : IsTranscendenceBasis R x :=
  isTranscendenceBasis_of_lift_trdeg_le_of_finite hx (by rwa [lift_id, lift_id])

end AlgebraicIndependent

variable (R S A)

/-
**lift_trdeg_add_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (R : Type u_1) (S : Type v) (A : Type w) [inst : CommRing R] [inst_1 : C
ommRing S] [inst_2 : CommRing A]   [inst_3 : Algebra R S] [inst_4 : Algebra R A]
 [inst_5 : Algebra S A] [IsScalarTower R S A] [Nontrivial R]   [NoZeroDivisors A
] [FaithfulSMul R S] [FaithfulSMul S A],   Cardinal.lift.{w, v} (Algebra.trdeg R
 S) + Cardinal.lift.{v, w} (Algebra.trdeg S A) =     Cardinal.lift.{v, w} (Algeb
ra.trdeg R A)
参数：R : Type u_1；S : Type v；A : Type w；Algebra.trdeg R S；Algebra.trdeg S A；Algebr
a.trdeg R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_isTranscendenceBasis`：exists_isTranscendenceBasis [FaithfulSMul R
 A] : exists s : Set A, IsTranscendenceBasis R ((↑) : s -> A)
· 使用定理 `Function.Injective.noZeroDivisors`：∀ {M₀ : Type u_1} {M₀' : Type u_3} [i
nst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : M
₀ → M₀'),   Function.In…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsTranscendenceBasis.cardinalMk_eq_trdeg`：cardinalMk_eq_trdeg {ι : Type 
w} {x : ι -> A} (hx : IsTranscendenceBasis R x) : #ι = trdeg R A
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `IsTranscendenceBasis.lift_cardinalMk_eq_trdeg`：lift_cardinalMk_eq_trdeg 
(hx : IsTranscendenceBasis R x) : lift.{w} #ι = lift.{u} (trdeg R A)
· 使用定理 `IsTranscendenceBasis.sumElim_comp`：IsTranscendenceBasis.sumElim_comp [No
ZeroDivisors A] {x : ι -> S} {y : ι' -> A} (hx : IsTranscendenceBasis R x) (hy :
 IsTranscendenceBasis S…
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
· 使用定理 `Cardinal.lift_add`：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = li
ft.{v} a + lift.{v} b
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
-/
@[stacks 030H] theorem lift_trdeg_add_eq [Nontrivial R] [NoZeroDivisors A] [FaithfulSMul R S]
    [FaithfulSMul S A] : lift.{w} (trdeg R S) + lift.{v} (trdeg S A) = lift.{v} (trdeg R A) := by
  have ⟨s, hs⟩ := exists_isTranscendenceBasis R S
  have ⟨t, ht⟩ := exists_isTranscendenceBasis S A
  have := (FaithfulSMul.algebraMap_injective S A).noZeroDivisors _ (map_zero _) (map_mul _)
  have := (FaithfulSMul.algebraMap_injective R S).nontrivial
  rw [← hs.cardinalMk_eq_trdeg, ← ht.cardinalMk_eq_trdeg, ← lift_umax.{w}, add_comm,
    ← (hs.sumElim_comp ht).lift_cardinalMk_eq_trdeg, mk_sum, lift_add, lift_lift, lift_lift]
/-
**trdeg_add_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (R : Type u_1) (S : Type v) [inst : CommRing R] [inst_1 : CommRing S] [i
nst_2 : Algebra R S] [Nontrivial R]   {A : Type v} [inst_4 : CommRing A] [NoZero
Divisors A] [inst_6 : Algebra R A] [inst_7 : Algebra S A] [FaithfulSMul R S]   [
FaithfulSMul S A] [IsScalarTower R S A], Algebra.trdeg R S + Algebra.trdeg S A =
 Algebra.trdeg R A
参数：R : Type u_1；S : Type v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `lift_trdeg_add_eq`：∀ (R : Type u_1) (S : Type v) (A : Type w) [inst : Co
mmRing R] [inst_1 : CommRing S] [inst_2 : CommRing A]   [inst_3 : Algebra R S] [
inst_4 …
-/
@[stacks 030H] theorem trdeg_add_eq [Nontrivial R] {A : Type v} [CommRing A] [NoZeroDivisors A]
    [Algebra R A] [Algebra S A] [FaithfulSMul R S] [FaithfulSMul S A] [IsScalarTower R S A] :
    trdeg R S + trdeg S A = trdeg R A := by
  rw [← (trdeg R S).lift_id, ← (trdeg S A).lift_id, ← (trdeg R A).lift_id]
  exact lift_trdeg_add_eq R S A

namespace IsTranscendenceBasis

variable {R S} [FaithfulSMul R S] [NoZeroDivisors S] (s : Set ι) (i j : ι) (v : ι → S)

/-- If `s` is a transcendence basis and `j` is algebraic over `s ∪ {i} \ {j}`,
then `s ∪ {i} \ {j}` is also a transcendence basis. -/
/-
**IsTranscendenceBasis.of_isAlgebraic_adjoin_insert_sdiff** 是 Mathlib 中的一个引理，位于命
名空间 `IsTranscendenceBasis`。
形式化陈述：of_isAlgebraic_adjoin_insert_sdiff (hj : j in insert i s) (H₁ : IsTranscen
denceBasis R fun x : s => v x) (H₂ : IsAlgebraic (Algebra.adjoin R (v '' (insert
 i s \ {j}))) (v j)) : IsTranscendenceBasis R fun x : ↥(insert i s \ {j}) => v x
参数：hj : j in insert i s；H₁ : IsTranscendenceBasis R fun x : s => v x；H₂ : IsAlge
braic (Algebra.adjoin R (v '' (insert i s \ {j}))) (v j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.nontrivial`：IsAlgebraic.nontrivial {a : A} (h : IsAlgebraic 
R a) : Nontrivial R
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用引理 `Subsemiring.subtype_injective`：subtype_injective : Function.Injective s.
subtype
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isDomain_iff_noZeroDivisors_and_nontrivial`：isDomain_iff_noZeroDivisors_
and_nontrivial [Ring α] : IsDomain α ↔ NoZeroDivisors α ∧ Nontrivial α
· 使用定理 `Module.nontrivial`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZer
o R] [Nontrivial M] [inst_2 : Zero M] [MulActionWithZero R M],   Nontrivial R
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
· 使用定理 `AlgebraicIndependent.injective`：∀ {ι : Type u} {R : Type u_2} {A : Type 
v} {x : ι → A} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],
   AlgebraicIndepend…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `AlgebraicIndependent.matroid_isBase_iff`：matroid_isBase_iff {s : Set A} 
: (matroid R A).IsBase s ↔ IsTranscendenceBasis R ((↑) : s -> A)
· 使用定理 `IsTranscendenceBasis.to_subtype_range`：IsTranscendenceBasis.to_subtype_r
ange (hx : IsTranscendenceBasis R x) : IsTranscendenceBasis R ((↑) : range x -> 
A)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.insert_sdiff_self_of_notMem`：insert_sdiff_self_of_notMem (h : a ∉ s)
 : insert a s \ {a} = s
· 使用定理 `AlgebraicIndependent.matroid_closure_eq`：matroid_closure_eq [IsDomain A]
 {s : Set A} : (matroid R A).closure s = algebraicClosure (adjoin R s) A
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Subalgebra.mem_algebraicClosure`：Subalgebra.mem_algebraicClosure [IsDoma
in R] {x : S} : x in algebraicClosure R S ↔ IsAlgebraic R x
· 使用定理 `Matroid.Indep.notMem_closure_sdiff_of_mem`：∀ {α : Type u_2} {M : Matroid
 α} {e : α} {I : Set α}, M.Indep I → e ∈ I → e ∉ M.closure (I \ {e})
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Set.InjOn.image_sdiff_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α
} {f : α → β} {t : Set α},   Set.InjOn f s → t ⊆ s → f '' (s \ t) = f '' s \ f '
' t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
If `s` is a transcendence basis and `j` is algebraic over `s ∪ {i} \ {j}`,
then `s ∪ {i} \ {j}` is also a transcendence basis.
-/
lemma of_isAlgebraic_adjoin_insert_sdiff (hj : j ∈ insert i s)
    (H₁ : IsTranscendenceBasis R fun x : s ↦ v x)
    (H₂ : IsAlgebraic (Algebra.adjoin R (v '' (insert i s \ {j}))) (v j)) :
    IsTranscendenceBasis R fun x : ↥(insert i s \ {j}) ↦ v x := by
  have := H₂.nontrivial
  have := (adjoin R (v '' (insert i s \ {j}))).subtype_injective.nontrivial
  have := (isDomain_iff_noZeroDivisors_and_nontrivial S).mpr ⟨‹_›, ‹_›⟩
  have := Module.nontrivial R S
  rw [← mem_algebraicClosure, ← SetLike.mem_coe, ← matroid_closure_eq] at H₂
  have inj := injOn_iff_injective.mpr H₁.1.injective
  have H' := image_eq_range .. ▸ matroid_isBase_iff.mpr H₁.to_subtype_range
  obtain hj' | hj := (em (j ∈ s)).symm
  · cases hj.resolve_right hj'; rwa [insert_sdiff_self_of_notMem hj']
  have Hj := H'.indep.notMem_closure_sdiff_of_mem ⟨j, hj, rfl⟩
  have hi : i ∉ s := fun hi ↦ Hj <| by
    rw [← image_singleton, ← inj.image_sdiff_subset (singleton_subset_iff.mpr hj)]
    rwa [insert_eq_of_mem hi] at H₂
  obtain eq | ne := eq_or_ne (v i) (v j)
  · classical
    convert!
      H₁.comp_equiv <|
        .symm <|
          ((Equiv.swap j i).image s).trans <|
            .setCongr <| Equiv.image_swap_of_mem_of_notMem hj hi with
      ⟨x, rfl | hxi, hxj⟩
    · simp [eq]
    · simp [Equiv.swap_apply_of_ne_of_ne hxj (ne_of_mem_of_not_mem hxi hi)]
  have hi' : v i ∉ v '' s := fun his ↦ Hj <| by
    refine Matroid.closure_subset_closure _ ?_ H₂
    rintro x ⟨k, ⟨rfl | hks, hkj⟩, rfl⟩
    · exact ⟨his, ne⟩
    · exact ⟨⟨k, hks, rfl⟩, inj.ne hks hj hkj⟩
  have : (insert i s).InjOn v := (injOn_insert hi).mpr ⟨inj, hi'⟩
  rw [← isTranscendenceBasis_subtype_range
    (by exact injOn_iff_injective.1 (this.mono sdiff_subset)),
    ← matroid_isBase_iff, ← image_eq_range]
  rw [this.image_sdiff_subset (singleton_subset_iff.mpr (.inr hj)), image_singleton,
    image_insert_eq] at H₂ ⊢
  exact H'.isBase_insert_sdiff_of_mem_closure H₂ (.inr ⟨j, hj, rfl⟩)

@[deprecated (since := "2026-06-03")]
alias of_isAlgebraic_adjoin_insert_diff := of_isAlgebraic_adjoin_insert_sdiff
/-
**IsTranscendenceBasis.of_isAlgebraic_adjoin_image_compl** 是 Mathlib 中的一个引理，位于命名
空间 `IsTranscendenceBasis`。
形式化陈述：of_isAlgebraic_adjoin_image_compl (H₁ : IsTranscendenceBasis R fun x : {x 
// x != i} => v x) (H₂ : IsAlgebraic (Algebra.adjoin R (v '' {j}ᶜ)) (v j)) : IsT
ranscendenceBasis R fun x : {x // x != j} => v x
参数：H₁ : IsTranscendenceBasis R fun x : {x // x != i} => v x；H₂ : IsAlgebraic (Al
gebra.adjoin R (v '' {j}ᶜ)) (v j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用引理 `IsTranscendenceBasis.of_isAlgebraic_adjoin_insert_sdiff`：of_isAlgebraic_
adjoin_insert_sdiff (hj : j in insert i s) (H₁ : IsTranscendenceBasis R fun x : 
s => v x) (H₂ : IsAlgebraic (Algebra.adjoin R…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `Set.insert_sdiff_self_of_mem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ 
s → insert a (s \ {a}) = s
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
lemma of_isAlgebraic_adjoin_image_compl
    (H₁ : IsTranscendenceBasis R fun x : {x // x ≠ i} ↦ v x)
    (H₂ : IsAlgebraic (Algebra.adjoin R (v '' {j}ᶜ)) (v j)) :
    IsTranscendenceBasis R fun x : {x // x ≠ j} ↦ v x := by
  obtain rfl | ne := eq_or_ne j i
  · exact H₁
  have := H₁.of_isAlgebraic_adjoin_insert_sdiff {i}ᶜ i j v (.inr ne)
  rw [compl_eq_univ_sdiff, insert_sdiff_self_of_mem (mem_univ _), ← compl_eq_univ_sdiff] at this
  exact this H₂

end IsTranscendenceBasis

