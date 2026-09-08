/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Data.DFinsupp.Lex
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.GameAdd
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Tactic.AdaptationNote

/-!
# Well-foundedness of the lexicographic and product orders on `DFinsupp` and `Pi`

The primary results are `DFinsupp.Lex.wellFounded` and the two variants that follow it,
which essentially say that if `(· > ·)` is a well order on `ι`, `(· < ·)` is well-founded on each
`α i`, and `0` is a bottom element in `α i`, then the lexicographic `(· < ·)` is well-founded
on `Π₀ i, α i`. The proof is modelled on the proof of `WellFounded.cutExpand`.

The results are used to prove `Pi.Lex.wellFounded` and two variants, which say that if
`ι` is finite and equipped with a linear order and `(· < ·)` is well-founded on each `α i`,
then the lexicographic `(· < ·)` is well-founded on `Π i, α i`, and the same is true for
`Π₀ i, α i` (`DFinsupp.Lex.wellFounded_of_finite`), because `DFinsupp` is order-isomorphic
to `pi` when `ι` is finite.

Finally, we deduce `DFinsupp.wellFoundedLT`, `Pi.wellFoundedLT`,
`DFinsupp.wellFoundedLT_of_finite` and variants, which concern the product order
rather than the lexicographic one. An order on `ι` is not required in these results,
but we deduce them from the well-foundedness of the lexicographic order by choosing
a well order on `ι` so that the product order `(· < ·)` becomes a subrelation
of the lexicographic `(· < ·)`.

All results are provided in two forms whenever possible: a general form where the relations
can be arbitrary (not the `(· < ·)` of a preorder, or not even transitive, etc.) and a specialized
form provided as `WellFoundedLT` instances where the `(d)Finsupp/pi` type (or their `Lex`
type synonyms) carries a natural `(· < ·)`.

Notice that the definition of `DFinsupp.Lex` says that `x < y` according to `DFinsupp.Lex r s`
iff there exists a coordinate `i : ι` such that `x i < y i` according to `s i`, and at all
`r`-smaller coordinates `j` (i.e. satisfying `r j i`), `x` remains unchanged relative to `y`;
in other words, coordinates `j` such that `¬ r j i` and `j ≠ i` are exactly where changes
can happen arbitrarily. This explains the appearance of `rᶜ ⊓ (≠)` in
`dfinsupp.acc_single` and `dfinsupp.well_founded`. When `r` is trichotomous (e.g. the `(· < ·)`
of a linear order), `¬ r j i ∧ j ≠ i` implies `r i j`, so it suffices to require `r.swap`
to be well-founded.
-/

public section


variable {ι : Type*} {α : ι → Type*}

namespace DFinsupp

open Relation Prod

section Zero

variable [∀ i, Zero (α i)] (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop)

set_option backward.isDefEq.respectTransparency false in
/-- This key lemma says that if a finitely supported dependent function `x₀` is obtained by merging
  two such functions `x₁` and `x₂`, and if we evolve `x₀` down the `DFinsupp.Lex` relation one
  step and get `x`, we can always evolve one of `x₁` and `x₂` down the `DFinsupp.Lex` relation
  one step while keeping the other unchanged, and merge them back (possibly in a different way)
  to get back `x`. In other words, the two parts evolve essentially independently under
  `DFinsupp.Lex`. This is used to show that a function `x` is accessible if
  `DFinsupp.single i (x i)` is accessible for each `i` in the (finite) support of `x`
  (`DFinsupp.Lex.acc_of_single`). -/
/-
**DFinsupp.lex_fibration** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：lex_fibration [forall (i) (s : Set ι), Decidable (i in s)] : Fibration (In
vImage (GameAdd (DFinsupp.Lex r s) (DFinsupp.Lex r s)) snd) (DFinsupp.Lex r s) f
un x => piecewise x.2.1 x.2.2 x.1
参数：i；s : Set ι；i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.not_imp`：∀ {a b : Prop}, ¬(a → b) ↔ a ∧ ¬b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
This key lemma says that if a finitely supported dependent function `x₀` is obta
ined by merging
  two such functions `x₁` and `x₂`, and if we evolve `x₀` down the `DFinsupp.Lex
` relation one
  step and get `x`, we can always evolve one of `x₁` and `x₂` down the `DFinsupp
.Lex` relation
  one step while keeping the other unchanged, and merge them back (possibly in a
 different way)
  to get back `x`. In other words, the two parts evolve essentially independentl
y under
  `DFinsupp.Lex`. This is used to show that a function `x` is accessible if
  `DFinsupp.single i (x i)` is accessible for each `i` in the (finite) support o
f `x`
  (`DFinsupp.Lex.acc_of_single`).
-/
theorem lex_fibration [∀ (i) (s : Set ι), Decidable (i ∈ s)] :
    Fibration (InvImage (GameAdd (DFinsupp.Lex r s) (DFinsupp.Lex r s)) snd) (DFinsupp.Lex r s)
      fun x => piecewise x.2.1 x.2.2 x.1 := by
  rintro ⟨p, x₁, x₂⟩ x ⟨i, hr, hs⟩
  simp_rw [piecewise_apply] at hs hr
  split_ifs at hs with hp
  · refine ⟨⟨{ j | r j i → j ∈ p }, piecewise x₁ x { j | r j i }, x₂⟩,
      .fst ⟨i, fun j hj ↦ ?_, ?_⟩, ?_⟩ <;> simp only [piecewise_apply, Set.mem_ofPred_eq]
    · simp only [if_pos hj]
    · split_ifs with hi
      · rwa [hr i hi, if_pos hp] at hs
      · assumption
    · ext1 j
      simp only [piecewise_apply, Set.mem_ofPred_eq]
      split_ifs with h₁ h₂ <;> try rfl
      · rw [hr j h₂, if_pos (h₁ h₂)]
      · rw [Classical.not_imp] at h₁
        rw [hr j h₁.1, if_neg h₁.2]
  · refine ⟨⟨{ j | r j i ∧ j ∈ p }, x₁, piecewise x₂ x { j | r j i }⟩,
      .snd ⟨i, fun j hj ↦ ?_, ?_⟩, ?_⟩ <;> simp only [piecewise_apply, Set.mem_ofPred_eq]
    · exact if_pos hj
    · split_ifs with hi
      · rwa [hr i hi, if_neg hp] at hs
      · assumption
    · ext1 j
      simp only [piecewise_apply, Set.mem_ofPred_eq]
      split_ifs with h₁ h₂ <;> try rfl
      · rw [hr j h₁.1, if_pos h₁.2]
      · rw [hr j h₂, if_neg]
        simpa [h₂] using h₁

variable {r s}
/-
**DFinsupp.Lex.acc_of_single_erase** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] {r : ι →
 ι → Prop} {s : (i : ι) → α i → α i → Prop}   [inst_1 : DecidableEq ι] {x : Π₀ (
i : ι), α i} (i : ι),   (Acc (DFinsupp.Lex r s) fun₀ | i => x i) → Acc (DFinsupp
.Lex r s) (DFinsupp.erase i x) → Acc (DFinsupp.Lex r s) x
参数：i : ι；α i；i : ι；i : ι；i : ι；Acc (DFinsupp.Lex r s) fun₀ | i => x i；DFinsupp.L
ex r s；DFinsupp.erase i x；DFinsupp.Lex r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `DFinsupp.piecewise_single_erase`：piecewise_single_erase (x : Π₀ i, β i) 
(i : ι) : (single i (x i)).piecewise (x.erase i) {i} = x
· 使用定理 `Acc.of_fibration`：∀ {α : Type u_1} {β : Type u_2} {rα : α → α → Prop} {r
β : β → β → Prop} (f : α → β),   Relation.Fibration rα rβ f → ∀ {a : α}, Acc rα 
a → Ac…
· 使用定理 `DFinsupp.lex_fibration`：lex_fibration [forall (i) (s : Set ι), Decidable
 (i in s)] : Fibration (InvImage (GameAdd (DFinsupp.Lex r s) (DFinsupp.Lex r s))
 snd) (DFins…
· 使用定理 `InvImage.accessible`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} {a :
 α} (f : α → β), Acc r (f a) → Acc (InvImage r f) a
· 使用定理 `Acc.prod_gameAdd`：Acc.prod_gameAdd (ha : Acc rα a) (hb : Acc rβ b) : Acc
 (Prod.GameAdd rα rβ) (a, b)
-/
theorem Lex.acc_of_single_erase [DecidableEq ι] {x : Π₀ i, α i} (i : ι)
    (hs : Acc (DFinsupp.Lex r s) <| single i (x i)) (hu : Acc (DFinsupp.Lex r s) <| x.erase i) :
    Acc (DFinsupp.Lex r s) x := by
  classical
    convert! ←
      @Acc.of_fibration _ _ _ _ _ (lex_fibration r s) ⟨{ i }, _⟩
        (InvImage.accessible snd <| hs.prod_gameAdd hu)
    convert! piecewise_single_erase x i
/-
**DFinsupp.Lex.acc_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] {r : ι →
 ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ ⦃i : ι⦄ ⦃a : α i⦄, ¬s i a 0) →
 Acc (DFinsupp.Lex r s) 0
参数：i : ι；α i；i : ι；∀ ⦃i : ι⦄ ⦃a : α i⦄, ¬s i a 0；DFinsupp.Lex r s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Lex.acc_zero (hbot : ∀ ⦃i a⦄, ¬s i a 0) : Acc (DFinsupp.Lex r s) 0 :=
  Acc.intro 0 fun _ ⟨_, _, h⟩ => (hbot h).elim
/-
**DFinsupp.Lex.acc_of_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] {r : ι →
 ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ ⦃i : ι⦄ ⦃a : α i⦄, ¬s i a 0) →
     ∀ [inst_1 : DecidableEq ι] [inst_2 : (i : ι) → (x : α i) → Decidable (x ≠ 0
)] (x : Π₀ (i : ι), α i),       (∀ i ∈ x.support, Acc (DFinsupp.Lex r s) fun₀ | 
i => x i) → Acc (DFinsupp.Lex r s) x
参数：i : ι；α i；i : ι；∀ ⦃i : ι⦄ ⦃a : α i⦄, ¬s i a 0；i : ι；x : α i；x ≠ 0；x : Π₀ (i :
 ι), α i；∀ i ∈ x.support, Acc (DFinsupp.Lex r s) fun₀ | i => x i；DFinsupp.Lex r 
s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFinsupp.support_eq_empty`：support_eq_empty {f : Π₀ i, β i} : f.support 
= ∅ ↔ f = 0
· 使用定理 `DFinsupp.Lex.acc_zero`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : 
ι) → Zero (α i)] {r : ι → ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ ⦃i : 
ι⦄ ⦃a : α i…
· 使用定理 `DFinsupp.Lex.acc_of_single_erase`：∀ {ι : Type u_1} {α : ι → Type u_2} [i
nst : (i : ι) → Zero (α i)] {r : ι → ι → Prop} {s : (i : ι) → α i → α i → Prop} 
  [inst_1 : DecidableE…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `DFinsupp.support_erase`：support_erase (i : ι) (f : Π₀ i, β i) : (f.erase
 i).support = f.support.erase i
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `DFinsupp.erase_ne`：erase_ne {i i' : ι} {f : Π₀ i, β i} (h : i' != i) : (
f.erase i) i' = f i'
· 使用定理 `Membership.mem.ne_of_notMem`：∀ {α : Type u_1} {β : Type u_2} [inst : Mem
bership α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
-/
theorem Lex.acc_of_single (hbot : ∀ ⦃i a⦄, ¬s i a 0) [DecidableEq ι]
    [∀ (i) (x : α i), Decidable (x ≠ 0)] (x : Π₀ i, α i) :
    (∀ i ∈ x.support, Acc (DFinsupp.Lex r s) <| single i (x i)) → Acc (DFinsupp.Lex r s) x := by
  generalize ht : x.support = t; revert x
  classical
    induction t using Finset.induction with
    | empty =>
      intro x ht
      rw [support_eq_empty.1 ht]
      exact fun _ => Lex.acc_zero hbot
    | insert b t hb ih =>
      refine fun x ht h => Lex.acc_of_single_erase b (h b <| t.mem_insert_self b) ?_
      refine ih _ (by rw [support_erase, ht, Finset.erase_insert hb]) fun a ha => ?_
      rw [erase_ne (ha.ne_of_notMem hb)]
      exact h a (Finset.mem_insert_of_mem ha)
/-
**DFinsupp.Lex.acc_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] {r : ι →
 ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ ⦃i : ι⦄ ⦃a : α i⦄, ¬s i a 0) →
     (∀ (i : ι), WellFounded (s i)) →       ∀ [inst_1 : DecidableEq ι] {i : ι}, 
        Acc (rᶜ ⊓ fun x1 x2 => x1 ≠ x2) i → ∀ (a : α i), Acc (DFinsupp.Lex r s) 
fun₀ | i => a
参数：i : ι；α i；i : ι；∀ ⦃i : ι⦄ ⦃a : α i⦄, ¬s i a 0；∀ (i : ι), WellFounded (s i)；rᶜ
 ⊓ fun x1 x2 => x1 ≠ x2；a : α i；DFinsupp.Lex r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.induction`：∀ {α : Sort u} {r : α → α → Prop},   WellFounded 
r → ∀ {C : α → Prop} (a : α), (∀ (x : α), (∀ (y : α), r y x → C y) → C x) → C a
· 使用定理 `DFinsupp.Lex.acc_of_single`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : 
(i : ι) → Zero (α i)] {r : ι → ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ 
⦃i : ι⦄ ⦃a : α i…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.single_eq_of_ne`：single_eq_of_ne {i i' b} (h : i' != i) : (sing
le i b : Π₀ i, β i) i' = 0
· 使用定理 `DFinsupp.single_zero`：single_zero (i) : (single i 0 : Π₀ i, β i) = 0
· 使用定理 `DFinsupp.Lex.acc_zero`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : 
ι) → Zero (α i)] {r : ι → ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ ⦃i : 
ι⦄ ⦃a : α i…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem Lex.acc_single (hbot : ∀ ⦃i a⦄, ¬s i a 0) (hs : ∀ i, WellFounded (s i))
    [DecidableEq ι] {i : ι} (hi : Acc (rᶜ ⊓ (· ≠ ·)) i) :
    ∀ a, Acc (DFinsupp.Lex r s) (single i a) := by
  induction hi with | _ i _ ih
  refine fun a => WellFounded.induction (hs i)
    (C := fun x ↦ Acc (DFinsupp.Lex r s) (single i x)) a fun a ha ↦ ?_
  refine Acc.intro _ fun x ↦ ?_
  rintro ⟨k, hr, hs⟩
  rw [single_apply] at hs
  split_ifs at hs with hik
  swap
  · exact (hbot hs).elim
  subst hik
  classical
    refine Lex.acc_of_single hbot x fun j hj ↦ ?_
    obtain rfl | hij := eq_or_ne j i
    · exact ha _ hs
    by_cases h : r j i
    · rw [hr j h, single_eq_of_ne hij, single_zero]
      exact Lex.acc_zero hbot
    · exact ih _ ⟨h, hij⟩ _
/-
**DFinsupp.Lex.acc** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] {r : ι →
 ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ ⦃i : ι⦄ ⦃a : α i⦄, ¬s i a 0) →
     (∀ (i : ι), WellFounded (s i)) →       ∀ [inst_1 : DecidableEq ι] [inst_2 :
 (i : ι) → (x : α i) → Decidable (x ≠ 0)] (x : Π₀ (i : ι), α i),         (∀ i ∈ 
x.support, Acc (rᶜ ⊓ fun x1 x2 => x1 ≠ x2) i) → Acc (DFinsupp.Lex r s) x
参数：i : ι；α i；i : ι；∀ ⦃i : ι⦄ ⦃a : α i⦄, ¬s i a 0；∀ (i : ι), WellFounded (s i)；i 
: ι；x : α i；x ≠ 0；x : Π₀ (i : ι), α i；∀ i ∈ x.support, Acc (rᶜ ⊓ fun x1 x2 => x1
 ≠ x2) i；DFinsupp.Lex r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.Lex.acc_of_single`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : 
(i : ι) → Zero (α i)] {r : ι → ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ 
⦃i : ι⦄ ⦃a : α i…
· 使用定理 `DFinsupp.Lex.acc_single`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i 
: ι) → Zero (α i)] {r : ι → ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ ⦃i 
: ι⦄ ⦃a : α i…
-/
theorem Lex.acc (hbot : ∀ ⦃i a⦄, ¬s i a 0) (hs : ∀ i, WellFounded (s i))
    [DecidableEq ι] [∀ (i) (x : α i), Decidable (x ≠ 0)] (x : Π₀ i, α i)
    (h : ∀ i ∈ x.support, Acc (rᶜ ⊓ (· ≠ ·)) i) : Acc (DFinsupp.Lex r s) x :=
  Lex.acc_of_single hbot x fun i hi => Lex.acc_single hbot hs (h i hi) _
/-
**DFinsupp.Lex.wellFounded** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] {r : ι →
 ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ ⦃i : ι⦄ ⦃a : α i⦄, ¬s i a 0) →
     (∀ (i : ι), WellFounded (s i)) → WellFounded (rᶜ ⊓ fun x1 x2 => x1 ≠ x2) → 
WellFounded (DFinsupp.Lex r s)
参数：i : ι；α i；i : ι；∀ ⦃i : ι⦄ ⦃a : α i⦄, ¬s i a 0；∀ (i : ι), WellFounded (s i)；rᶜ
 ⊓ fun x1 x2 => x1 ≠ x2；DFinsupp.Lex r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.Lex.acc`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → 
Zero (α i)] {r : ι → ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ ⦃i : ι⦄ ⦃a
 : α i…
· 使用定理 `WellFounded.apply`：∀ {α : Sort u} {r : α → α → Prop}, WellFounded r → ∀ 
(a : α), Acc r a
-/
theorem Lex.wellFounded (hbot : ∀ ⦃i a⦄, ¬s i a 0) (hs : ∀ i, WellFounded (s i))
    (hr : WellFounded <| rᶜ ⊓ (· ≠ ·)) : WellFounded (DFinsupp.Lex r s) :=
  ⟨fun x => by classical exact Lex.acc hbot hs x fun i _ => hr.apply i⟩
/-
**DFinsupp.Lex.wellFounded'** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] {r : ι →
 ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ ⦃i : ι⦄ ⦃a : α i⦄, ¬s i a 0) →
     (∀ (i : ι), WellFounded (s i)) →       ∀ [Std.Trichotomous r], WellFounded 
(Function.swap r) → WellFounded (DFinsupp.Lex r s)
参数：i : ι；α i；i : ι；∀ ⦃i : ι⦄ ⦃a : α i⦄, ¬s i a 0；∀ (i : ι), WellFounded (s i)；Fu
nction.swap r；DFinsupp.Lex r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.Lex.wellFounded`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i
 : ι) → Zero (α i)] {r : ι → ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ ⦃i
 : ι⦄ ⦃a : α i…
· 使用定理 `Subrelation.wf`：∀ {α : Sort u} {r q : α → α → Prop}, Subrelation q r → W
ellFounded r → WellFounded q
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
· 使用定理 `Std.Trichotomous.trichotomous`：∀ {α : Sort u} {r : α → α → Prop} [self :
 Std.Trichotomous r] (a b : α), ¬r a b → ¬r b a → a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Lex.wellFounded' (hbot : ∀ ⦃i a⦄, ¬s i a 0) (hs : ∀ i, WellFounded (s i))
    [Std.Trichotomous r] (hr : WellFounded (Function.swap r)) : WellFounded (DFinsupp.Lex r s) :=
  Lex.wellFounded hbot hs <| Subrelation.wf
    (fun {i j} h ↦ Not.imp_symm (@Std.Trichotomous.trichotomous ι r _ i j h.left) h.right) hr

end Zero

/-
**DFinsupp.Lex.wellFoundedLT** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : LT ι] [Std.Trichotomous fun x1
 x2 => x1 < x2] [hι : WellFoundedGT ι]   [inst_2 : (i : ι) → AddMonoid (α i)] [i
nst_3 : (i : ι) → PartialOrder (α i)] [∀ (i : ι), IsBotZeroClass (α i)]   [hα : 
∀ (i : ι), WellFoundedLT (α i)], WellFoundedLT (Lex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；i : ι；α i；i : ι；α i；Lex (Π₀ (i : ι), α i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.Lex.wellFounded'`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (
i : ι) → Zero (α i)] {r : ι → ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ ⦃
i : ι⦄ ⦃a : α i…
· 使用定理 `not_lt_zero`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], ¬a < 0
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
instance Lex.wellFoundedLT [LT ι] [@Std.Trichotomous ι (· < ·)] [hι : WellFoundedGT ι]
    [∀ i, AddMonoid (α i)] [∀ i, PartialOrder (α i)] [∀ i, IsBotZeroClass (α i)]
    [hα : ∀ i, WellFoundedLT (α i)] :
    WellFoundedLT (Lex (Π₀ i, α i)) :=
  ⟨Lex.wellFounded' (fun _ _ => not_lt_zero) (fun i => (hα i).wf) hι.wf⟩

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.Colex.wellFoundedLT** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Colex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : LT ι] [Std.Trichotomous fun x1
 x2 => x1 < x2] [WellFoundedLT ι]   [inst_3 : (i : ι) → AddMonoid (α i)] [inst_4
 : (i : ι) → PartialOrder (α i)] [∀ (i : ι), IsBotZeroClass (α i)]   [∀ (i : ι),
 WellFoundedLT (α i)], WellFoundedLT (Colex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；i : ι；α i；i : ι；α i；Colex (Π₀ (i : ι), α i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.Lex.wellFoundedLT`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : 
LT ι] [Std.Trichotomous fun x1 x2 => x1 < x2] [hι : WellFoundedGT ι]   [inst_2 :
 (i : ι) → AddMo…
· 使用定理 `OrderDual.instTrichotomousLt`：∀ {α : Type u_1} [inst : LT α] [T : Std.Tr
ichotomous LT.lt], Std.Trichotomous LT.lt
· 使用定理 `instWellFoundedGTOrderDualOfWellFoundedLT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedLT α], WellFoundedGT αᵒᵈ
-/
instance Colex.wellFoundedLT [LT ι] [@Std.Trichotomous ι (· < ·)] [WellFoundedLT ι]
    [∀ i, AddMonoid (α i)] [∀ i, PartialOrder (α i)] [∀ i, IsBotZeroClass (α i)]
    [∀ i, WellFoundedLT (α i)] :
    WellFoundedLT (Colex (Π₀ i, α i)) :=
  Lex.wellFoundedLT (ι := ιᵒᵈ)

end DFinsupp

open DFinsupp

variable (r : ι → ι → Prop) {s : ∀ i, α i → α i → Prop}

/-
**Pi.Lex.wellFounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.Lex.wellFounded [IsStrictTotalOrder ι r] [Finite ι] (hs : forall i, Wel
lFounded (s i)) : WellFounded (Pi.Lex r (fun {i} => s i))
参数：hs : forall i, WellFounded (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonForallOfFastIsEmpty`：∀ {α : Sort u} [inst 
: Meta.FastIsEmpty α] {β : α → Sort v}, Meta.FastSubsingleton ((x : α) → β x)
· 使用定理 `WellFoundedRelation.wf`：∀ {α : Sort u} [self : WellFoundedRelation α], W
ellFounded WellFoundedRelation.rel
· 使用定理 `trivial`：True
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `DFinsupp.Lex.wellFounded'`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (
i : ι) → Zero (α i)] {r : ι → ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ ⦃
i : ι⦄ ⦃a : α i…
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)
· 使用定理 `IsStrictTotalOrder.toTrichotomous`：∀ {α : Sort u_1} {lt : α → α → Prop} 
[self : IsStrictTotalOrder α lt], Std.Trichotomous lt
· 使用定理 `Finite.wellFounded_of_trans_of_irrefl`：wellFounded_of_trans_of_irrefl (r
 : α -> α -> Prop) [IsTrans α r] [Std.Irrefl r] : WellFounded r
· 使用定理 `Function.instIsTransSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [IsTra
ns α r], IsTrans α (Function.swap r)
· 使用定理 `IsStrictOrder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsS
trictOrder α r], IsTrans α r
· 使用定理 `IsStrictTotalOrder.toIsStrictOrder`：∀ {α : Sort u_1} {lt : α → α → Prop}
 [self : IsStrictTotalOrder α lt], IsStrictOrder α lt
· 使用定理 `Function.instIrreflSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Ir
refl r], Std.Irrefl (Function.swap r)
· 使用定理 `IsStrictOrder.toIrrefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsSt
rictOrder α r], Std.Irrefl r
-/
theorem Pi.Lex.wellFounded [IsStrictTotalOrder ι r] [Finite ι] (hs : ∀ i, WellFounded (s i)) :
    WellFounded (Pi.Lex r (fun {i} ↦ s i)) := by
  obtain h | ⟨⟨x⟩⟩ := isEmpty_or_nonempty (∀ i, α i)
  · convert! emptyWf.wf
  let : ∀ i, Zero (α i) := fun i => ⟨(hs i).min ⊤ ⟨x i, trivial⟩⟩
  have := Fintype.ofFinite ι
  refine InvImage.wf equivFunOnFintype.symm (Lex.wellFounded' (fun i a => ?_) hs ?_)
  exacts [(hs i).not_lt_min ⊤ trivial, Finite.wellFounded_of_trans_of_irrefl (Function.swap r)]
/-
**Pi.Lex.wellFoundedLT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.Lex.wellFoundedLT [LinearOrder ι] [Finite ι] [forall i, LT (α i)] [hwf 
: forall i, WellFoundedLT (α i)] : WellFoundedLT (Lex (forall i, α i))
参数：α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.Lex.wellFounded`：Pi.Lex.wellFounded [IsStrictTotalOrder ι r] [Finite 
ι] (hs : forall i, WellFounded (s i)) : WellFounded (Pi.Lex r (fun {i} => s i))
· 使用定理 `instIsStrictTotalOrderLt`：∀ {α : Type u} [inst : LinearOrder α], IsStric
tTotalOrder α fun x1 x2 => x1 < x2
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
instance Pi.Lex.wellFoundedLT [LinearOrder ι] [Finite ι] [∀ i, LT (α i)]
    [hwf : ∀ i, WellFoundedLT (α i)] : WellFoundedLT (Lex (∀ i, α i)) :=
  ⟨Pi.Lex.wellFounded (· < ·) fun i => (hwf i).1⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Pi.Colex.wellFoundedLT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.Colex.wellFoundedLT [LinearOrder ι] [Finite ι] [forall i, LT (α i)] [fo
rall i, WellFoundedLT (α i)] : WellFoundedLT (Colex (forall i, α i))
参数：α i；α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.Colex.wellFoundedLT [LinearOrder ι] [Finite ι] [∀ i, LT (α i)]
    [∀ i, WellFoundedLT (α i)] : WellFoundedLT (Colex (∀ i, α i)) :=
  Pi.Lex.wellFoundedLT (ι := ιᵒᵈ)
/-
**Function.Lex.wellFoundedLT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Function.Lex.wellFoundedLT {α} [LinearOrder ι] [Finite ι] [LT α] [WellFoun
dedLT α] : WellFoundedLT (Lex (ι -> α))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Function.Lex.wellFoundedLT {α} [LinearOrder ι] [Finite ι] [LT α] [WellFoundedLT α] :
    WellFoundedLT (Lex (ι → α)) :=
  Pi.Lex.wellFoundedLT
/-
**DFinsupp.Lex.wellFounded_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DFinsupp.Lex.wellFounded_of_finite [IsStrictTotalOrder ι r] [Finite ι] [fo
rall i, Zero (α i)] (hs : forall i, WellFounded (s i)) : WellFounded (DFinsupp.L
ex r s)
参数：α i；hs : forall i, WellFounded (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用定理 `Pi.Lex.wellFounded`：Pi.Lex.wellFounded [IsStrictTotalOrder ι r] [Finite 
ι] (hs : forall i, WellFounded (s i)) : WellFounded (Pi.Lex r (fun {i} => s i))
-/
theorem DFinsupp.Lex.wellFounded_of_finite [IsStrictTotalOrder ι r] [Finite ι] [∀ i, Zero (α i)]
    (hs : ∀ i, WellFounded (s i)) : WellFounded (DFinsupp.Lex r s) :=
  have := Fintype.ofFinite ι
  InvImage.wf equivFunOnFintype (Pi.Lex.wellFounded r hs)
/-
**DFinsupp.Lex.wellFoundedLT_of_finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：DFinsupp.Lex.wellFoundedLT_of_finite [LinearOrder ι] [Finite ι] [forall i,
 Zero (α i)] [forall i, LT (α i)] [hwf : forall i, WellFoundedLT (α i)] : WellFo
undedLT (Lex (Π₀ i, α i))
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.Lex.wellFounded_of_finite`：DFinsupp.Lex.wellFounded_of_finite [
IsStrictTotalOrder ι r] [Finite ι] [forall i, Zero (α i)] (hs : forall i, WellFo
unded (s i)) : WellFound…
· 使用定理 `instIsStrictTotalOrderLt`：∀ {α : Type u} [inst : LinearOrder α], IsStric
tTotalOrder α fun x1 x2 => x1 < x2
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
instance DFinsupp.Lex.wellFoundedLT_of_finite [LinearOrder ι] [Finite ι] [∀ i, Zero (α i)]
    [∀ i, LT (α i)] [hwf : ∀ i, WellFoundedLT (α i)] : WellFoundedLT (Lex (Π₀ i, α i)) :=
  ⟨DFinsupp.Lex.wellFounded_of_finite (· < ·) fun i => (hwf i).1⟩

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.Colex.wellFoundedLT_of_finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：DFinsupp.Colex.wellFoundedLT_of_finite [LinearOrder ι] [Finite ι] [forall 
i, Zero (α i)] [forall i, LT (α i)] [hwf : forall i, WellFoundedLT (α i)] : Well
FoundedLT (Colex (Π₀ i, α i))
参数：α i；α i；α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance DFinsupp.Colex.wellFoundedLT_of_finite [LinearOrder ι] [Finite ι] [∀ i, Zero (α i)]
    [∀ i, LT (α i)] [hwf : ∀ i, WellFoundedLT (α i)] : WellFoundedLT (Colex (Π₀ i, α i)) :=
  DFinsupp.Lex.wellFoundedLT_of_finite (ι := ιᵒᵈ)
/-
**DFinsupp.wellFoundedLT** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] [inst_1 
: (i : ι) → Preorder (α i)]   [∀ (i : ι), WellFoundedLT (α i)], (∀ ⦃i : ι⦄ ⦃a : 
α i⦄, ¬a < 0) → WellFoundedLT (Π₀ (i : ι), α i)
参数：i : ι；α i；i : ι；α i；i : ι；α i；∀ ⦃i : ι⦄ ⦃a : α i⦄, ¬a < 0；Π₀ (i : ι), α i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
· 使用定理 `DFinsupp.Lex.wellFounded'`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (
i : ι) → Zero (α i)] {r : ι → ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ ⦃
i : ι⦄ ⦃a : α i…
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `instWellFoundedLTAntisymmetrizationLe`：∀ {α : Type u_1} [inst : Preorder
 α] [WellFoundedLT α], WellFoundedLT (Antisymmetrization α fun x1 x2 => x1 ≤ x2)
· 使用定理 `Function.instTrichotomousSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [
Std.Trichotomous r], Std.Trichotomous (Function.swap r)
· 使用定理 `IsWellOrder.toTrichotomous`：∀ {α : Type u} {r : α → α → Prop} [self : Is
WellOrder α r], Std.Trichotomous r
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `Subrelation.wf`：∀ {α : Sort u} {r q : α → α → Prop}, Subrelation q r → W
ellFounded r → WellFounded q
· 使用定理 `DFinsupp.lex_lt_of_lt_of_preorder`：lex_lt_of_lt_of_preorder [forall i, P
reorder (α i)] (r) [IsStrictOrder ι r] {x y : Π₀ i, α i} (hlt : x < y) : exists 
i, (forall j, r j i -> …
· 使用定理 `Function.instIsStrictOrderSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) 
[IsStrictOrder α r], IsStrictOrder α (Function.swap r)
· 使用定理 `IsStrictTotalOrder.toIsStrictOrder`：∀ {α : Sort u_1} {lt : α → α → Prop}
 [self : IsStrictTotalOrder α lt], IsStrictOrder α lt
· 使用定理 `instIsStrictTotalOrderOfIsWellOrder`：∀ {α : Type u_1} (r : α → α → Prop)
 [IsWellOrder α r], IsStrictTotalOrder α r
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
-/
protected theorem DFinsupp.wellFoundedLT [∀ i, Zero (α i)] [∀ i, Preorder (α i)]
    [∀ i, WellFoundedLT (α i)] (hbot : ∀ ⦃i⦄ ⦃a : α i⦄, ¬a < 0) : WellFoundedLT (Π₀ i, α i) :=
  ⟨by
    set β := fun i ↦ Antisymmetrization (α i) (· ≤ ·)
    set e : (i : ι) → α i → β i := fun i ↦ toAntisymmetrization (· ≤ ·)
    let _ : ∀ i, Zero (β i) := fun i ↦ ⟨e i 0⟩
    have : WellFounded (DFinsupp.Lex (Function.swap <| @WellOrderingRel ι)
        (fun _ ↦ (· < ·) : (i : ι) → β i → β i → Prop)) := by
      refine Lex.wellFounded' ?_ (fun i ↦ IsWellFounded.wf) ?_
      · rintro i ⟨a⟩
        apply hbot
      · simp +unfoldPartialApp only [Function.swap]
        exact IsWellFounded.wf
    refine Subrelation.wf (fun h => ?_) <| InvImage.wf (mapRange e fun _ ↦ rfl) this
    obtain ⟨i, he, hl⟩ := lex_lt_of_lt_of_preorder (Function.swap WellOrderingRel) h
    exact ⟨i, fun j hj ↦ Quot.sound (he j hj), hl⟩⟩
/-
**DFinsupp.wellFoundedLT'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：DFinsupp.wellFoundedLT' [forall i, AddMonoid (α i)] [forall i, PartialOrde
r (α i)] [forall i, IsBotZeroClass (α i)] [forall i, WellFoundedLT (α i)] : Well
FoundedLT (Π₀ i, α i)
参数：α i；α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.wellFoundedLT`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i :
 ι) → Zero (α i)] [inst_1 : (i : ι) → Preorder (α i)]   [∀ (i : ι), WellFoundedL
T (α i)], (∀…
· 使用定理 `not_lt_zero`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], ¬a < 0
-/
instance DFinsupp.wellFoundedLT'
    [∀ i, AddMonoid (α i)] [∀ i, PartialOrder (α i)] [∀ i, IsBotZeroClass (α i)]
    [∀ i, WellFoundedLT (α i)] : WellFoundedLT (Π₀ i, α i) :=
  DFinsupp.wellFoundedLT fun _ _ => not_lt_zero
/-
**Pi.wellFoundedLT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.wellFoundedLT [Finite ι] [forall i, Preorder (α i)] [hw : forall i, Wel
lFoundedLT (α i)] : WellFoundedLT (forall i, α i)
参数：α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonForallOfFastIsEmpty`：∀ {α : Sort u} [inst 
: Meta.FastIsEmpty α] {β : α → Sort v}, Meta.FastSubsingleton ((x : α) → β x)
· 使用定理 `WellFoundedRelation.wf`：∀ {α : Sort u} [self : WellFoundedRelation α], W
ellFounded WellFoundedRelation.rel
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `trivial`：True
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `DFinsupp.wellFoundedLT`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i :
 ι) → Zero (α i)] [inst_1 : (i : ι) → Preorder (α i)]   [∀ (i : ι), WellFoundedL
T (α i)], (∀…
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)
-/
instance Pi.wellFoundedLT [Finite ι] [∀ i, Preorder (α i)] [hw : ∀ i, WellFoundedLT (α i)] :
    WellFoundedLT (∀ i, α i) :=
  ⟨by
    obtain h | ⟨⟨x⟩⟩ := isEmpty_or_nonempty (∀ i, α i)
    · convert! emptyWf.wf
    let : ∀ i, Zero (α i) := fun i => ⟨(hw i).wf.min ⊤ ⟨x i, trivial⟩⟩
    have := Fintype.ofFinite ι
    refine InvImage.wf equivFunOnFintype.symm (DFinsupp.wellFoundedLT fun i a => ?_).wf
    exact (hw i).wf.not_lt_min ⊤ trivial⟩
/-
**Function.wellFoundedLT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Function.wellFoundedLT {α} [Finite ι] [Preorder α] [WellFoundedLT α] : Wel
lFoundedLT (ι -> α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Function.wellFoundedLT {α} [Finite ι] [Preorder α] [WellFoundedLT α] :
    WellFoundedLT (ι → α) :=
  Pi.wellFoundedLT
/-
**DFinsupp.wellFoundedLT_of_finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：DFinsupp.wellFoundedLT_of_finite [Finite ι] [forall i, Zero (α i)] [forall
 i, Preorder (α i)] [forall i, WellFoundedLT (α i)] : WellFoundedLT (Π₀ i, α i)
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
instance DFinsupp.wellFoundedLT_of_finite [Finite ι] [∀ i, Zero (α i)] [∀ i, Preorder (α i)]
    [∀ i, WellFoundedLT (α i)] : WellFoundedLT (Π₀ i, α i) :=
  have := Fintype.ofFinite ι
  ⟨InvImage.wf equivFunOnFintype Pi.wellFoundedLT.wf⟩
