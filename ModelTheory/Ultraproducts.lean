/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.Quotients
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Order.Filter.Ultrafilter.Defs

/-!
# Ultraproducts and Łoś's Theorem

## Main Definitions

- `FirstOrder.Language.Ultraproduct.Structure` is the ultraproduct structure on `Filter.Product`.

## Main Results

- Łoś's Theorem: `FirstOrder.Language.Ultraproduct.sentence_realize`. An ultraproduct models a
  sentence `φ` if and only if the set of structures in the product that model `φ` is in the
  ultrafilter.

## Tags

ultraproduct, Los's theorem
-/

public section

universe u v

variable {α : Type*} (M : α → Type*) (u : Ultrafilter α)

open FirstOrder Filter

namespace FirstOrder

namespace Language

open Structure

variable {L : Language.{u, v}} [∀ a, L.Structure (M a)]

namespace Ultraproduct

/-
**FirstOrder.Language.Ultraproduct.setoidPrestructure** 是 Mathlib 中的一个实例，位于命名空间 
`FirstOrder.Language.Ultraproduct`。
形式化陈述：setoidPrestructure : L.Prestructure ((u : Filter α).productSetoid M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance setoidPrestructure : L.Prestructure ((u : Filter α).productSetoid M) :=
  { (u : Filter α).productSetoid M with
    toStructure :=
      { funMap := fun {_} f x a => funMap f fun i => x i a
        RelMap := fun {_} r x => ∀ᶠ a : α in u, RelMap r fun i => x i a }
    fun_equiv := fun {n} f x y xy => by
      refine mem_of_superset (iInter_mem.2 xy) fun a ha => ?_
      simp only [Set.mem_iInter, Set.mem_ofPred_eq] at ha
      simp only [Set.mem_ofPred_eq, ha]
    rel_equiv := fun {n} r x y xy => by
      rw [← iff_eq_eq]
      refine ⟨fun hx => ?_, fun hy => ?_⟩
      · refine mem_of_superset (inter_mem hx (iInter_mem.2 xy)) ?_
        rintro a ⟨ha1, ha2⟩
        simp only [Set.mem_iInter, Set.mem_ofPred_eq] at *
        rw [← funext ha2]
        exact ha1
      · refine mem_of_superset (inter_mem hy (iInter_mem.2 xy)) ?_
        rintro a ⟨ha1, ha2⟩
        simp only [Set.mem_iInter, Set.mem_ofPred_eq] at *
        rw [funext ha2]
        exact ha1 }

variable {M} {u}
/-
**FirstOrder.Language.Ultraproduct.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Langua
ge.Ultraproduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance «structure» : L.Structure ((u : Filter α).Product M) :=
  inferInstanceAs <| L.Structure (Quotient _)
/-
**FirstOrder.Language.Ultraproduct.funMap_cast** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.Ultraproduct`。
形式化陈述：funMap_cast {n : Nat} (f : L.Functions n) (x : Fin n -> forall a, M a) : (
funMap f fun i => (x i : (u : Filter α).Product M)) = (fun a => funMap f fun i =
> x i a : (u : Filter α).Product M)
参数：f : L.Functions n；x : Fin n -> forall a, M a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.funMap_quotient_mk'`：funMap_quotient_mk' {n : Nat} (
f : L.Functions n) (x : Fin n -> M) : (funMap f fun i => (⟦x i⟧ : Quotient s)) =
 ⟦@funMap _ _ ps.toStructure …
-/
theorem funMap_cast {n : ℕ} (f : L.Functions n) (x : Fin n → ∀ a, M a) :
    (funMap f fun i => (x i : (u : Filter α).Product M)) =
      (fun a => funMap f fun i => x i a : (u : Filter α).Product M) := by
  apply funMap_quotient_mk'
/-
**FirstOrder.Language.Ultraproduct.term_realize_cast** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.Ultraproduct`。
形式化陈述：term_realize_cast {β : Type*} (x : β -> forall a, M a) (t : L.Term β) : (t
.realize fun i => (x i : (u : Filter α).Product M)) = (fun a => t.realize fun i 
=> x i a : (u : Filter α).Product M)
参数：x : β -> forall a, M a；t : L.Term β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Term.realize_quotient_mk'`：∀ {L : FirstOrder.Languag
e} {M : Type u_1} (s : Setoid M) [ps : L.Prestructure s] {β : Type u_2} (t : L.T
erm β)   (x : β → M), FirstOrder.La…
-/
theorem term_realize_cast {β : Type*} (x : β → ∀ a, M a) (t : L.Term β) :
    (t.realize fun i => (x i : (u : Filter α).Product M)) =
      (fun a => t.realize fun i => x i a : (u : Filter α).Product M) := by
  convert!
    @Term.realize_quotient_mk' L _ ((u : Filter α).productSetoid M)
      (Ultraproduct.setoidPrestructure M u) _ t x using 2
  ext a
  induction t with
  | var => rfl
  | func _ _ t_ih => simp only [Term.realize, t_ih]; rfl

variable [∀ a : α, Nonempty (M a)]
/-
**FirstOrder.Language.Ultraproduct.boundedFormula_realize_cast** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language.Ultraproduct`。
形式化陈述：boundedFormula_realize_cast {β : Type*} {n : Nat} (φ : L.BoundedFormula β 
n) (x : β -> forall a, M a) (v : Fin n -> forall a, M a) : (φ.Realize (fun i : β
 => (x i : (u : Filter α).Product M)) (fun i => (v i : (u : Filter α).Product M)
)) ↔ forallᶠ a : α in u, φ.Realize (fun i : β => x i a) fun i => v i a
参数：φ : L.BoundedFormula β n；x : β -> forall a, M a；v : Fin n -> forall a, M a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sum.comp_elim`：∀ {γ : Sort u_1} {δ : Sort u_2} {α : Type u_3} {β : Type 
u_4} (f : γ → δ) (g : α → γ) (h : β → γ),   f ∘ Sum.elim g h = Sum.elim (f ∘ g) 
(f …
· 使用定理 `FirstOrder.Language.Ultraproduct.term_realize_cast`：term_realize_cast {β
 : Type*} (x : β -> forall a, M a) (t : L.Term β) : (t.realize fun i => (x i : (
u : Filter α).Product M)) = (fun a => t.…
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
· 使用定理 `FirstOrder.Language.relMap_quotient_mk'`：relMap_quotient_mk' {n : Nat} (
r : L.Relations n) (x : Fin n -> M) : (RelMap r fun i => (⟦x i⟧ : Quotient s)) ↔
 @RelMap _ _ ps.toStructure _…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ultrafilter.eventually_imp`：eventually_imp : (forallᶠ x in f, p x -> q x
) ↔ (forallᶠ x in f, p x) -> forallᶠ x in f, q x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Quotient.forall`：Quotient.forall {α : Sort*} {s : Setoid α} {p : Quotien
t s -> Prop} : (forall a, p a) ↔ forall a : α, p ⟦a⟧
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Classical.epsilon_spec`：∀ {α : Sort u} {p : α → Prop} (hex : ∃ y, p y), 
p (Classical.epsilon p)
· 使用定理 `Filter.eventually_iff`：eventually_iff {f : Filter α} {P : α -> Prop} : (
forallᶠ x in f, P x) ↔ { x | P x } in f
-/
theorem boundedFormula_realize_cast {β : Type*} {n : ℕ} (φ : L.BoundedFormula β n)
    (x : β → ∀ a, M a) (v : Fin n → ∀ a, M a) :
    (φ.Realize (fun i : β => (x i : (u : Filter α).Product M))
        (fun i => (v i : (u : Filter α).Product M))) ↔
      ∀ᶠ a : α in u, φ.Realize (fun i : β => x i a) fun i => v i a := by
  induction φ with
  | falsum => simp only [BoundedFormula.Realize, eventually_const]
  | equal =>
    have h2 : ∀ a : α, (Sum.elim (fun i : β => x i a) fun i => v i a) = fun i => Sum.elim x v i a :=
      fun a => funext fun i => Sum.casesOn i (fun i => rfl) fun i => rfl
    simp only [BoundedFormula.Realize, h2]
    erw [(Sum.comp_elim ((↑) : (∀ a, M a) → (u : Filter α).Product M) x v).symm,
      term_realize_cast, term_realize_cast]
    exact Quotient.eq''
  | rel =>
    have h2 : ∀ a : α, (Sum.elim (fun i : β => x i a) fun i => v i a) = fun i => Sum.elim x v i a :=
      fun a => funext fun i => Sum.casesOn i (fun i => rfl) fun i => rfl
    simp only [BoundedFormula.Realize, h2]
    erw [(Sum.comp_elim ((↑) : (∀ a, M a) → (u : Filter α).Product M) x v).symm]
    conv_lhs => enter [2, i]; erw [term_realize_cast]
    apply relMap_quotient_mk'
  | imp _ _ ih ih' =>
    simp only [BoundedFormula.Realize, ih v, ih' v]
    rw [Ultrafilter.eventually_imp]
  | @all k φ ih =>
    simp only [BoundedFormula.Realize]
    apply Iff.trans (b := ∀ m : ∀ a : α, M a,
      φ.Realize (fun i : β => (x i : (u : Filter α).Product M))
        (Fin.snoc (((↑) : (∀ a, M a) → (u : Filter α).Product M) ∘ v)
          (m : (u : Filter α).Product M)))
    · exact Quotient.forall
    have h' :
      ∀ (m : ∀ a, M a) (a : α),
        (fun i : Fin (k + 1) => (Fin.snoc v m : _ → ∀ a, M a) i a) =
          Fin.snoc (fun i : Fin k => v i a) (m a) := by
      refine fun m a => funext (Fin.reverseInduction ?_ fun i _ => ?_)
      · simp only [Fin.snoc_last]
      · simp only [Fin.snoc_castSucc]
    simp only [← Fin.comp_snoc]
    simp only [Function.comp_def, ih, h']
    refine ⟨fun h => ?_, fun h m => ?_⟩
    · contrapose! h
      refine
        ⟨fun a : α =>
          Classical.epsilon fun m : M a =>
            ¬φ.Realize (fun i => x i a) (Fin.snoc (fun i => v i a) m),
          ?_⟩
      exact Filter.mem_of_superset h fun a ha => Classical.epsilon_spec ha
    · rw [Filter.eventually_iff] at *
      exact Filter.mem_of_superset h fun a ha => ha (m a)
/-
**FirstOrder.Language.Ultraproduct.realize_formula_cast** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.Ultraproduct`。
形式化陈述：realize_formula_cast {β : Type*} (φ : L.Formula β) (x : β -> forall a, M a
) : (φ.Realize fun i => (x i : (u : Filter α).Product M)) ↔ forallᶠ a : α in u, 
φ.Realize fun i => x i a
参数：φ : L.Formula β；x : β -> forall a, M a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Ultraproduct.boundedFormula_realize_cast`：boundedFor
mula_realize_cast {β : Type*} {n : Nat} (φ : L.BoundedFormula β n) (x : β -> for
all a, M a) (v : Fin n -> forall a, M a) : (φ.Real…
· 使用引理 `iff_eq_eq`：iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem realize_formula_cast {β : Type*} (φ : L.Formula β) (x : β → ∀ a, M a) :
    (φ.Realize fun i => (x i : (u : Filter α).Product M)) ↔
      ∀ᶠ a : α in u, φ.Realize fun i => x i a := by
  simp_rw [Formula.Realize, ← boundedFormula_realize_cast φ x, iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)

/-- **Łoś's Theorem**: A sentence is true in an ultraproduct if and only if the set of structures
it is true in is in the ultrafilter. -/
/-
**FirstOrder.Language.Ultraproduct.sentence_realize** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.Ultraproduct`。
形式化陈述：sentence_realize (φ : L.Sentence) : (u : Filter α).Product M ⊨ φ ↔ forallᶠ
 a : α in u, M a ⊨ φ
参数：φ : L.Sentence。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Ultraproduct.realize_formula_cast`：realize_formula_c
ast {β : Type*} (φ : L.Formula β) (x : β -> forall a, M a) : (φ.Realize fun i =>
 (x i : (u : Filter α).Product M)) ↔ forall…
· 使用引理 `iff_eq_eq`：iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
**Łoś's Theorem**: A sentence is true in an ultraproduct if and only if the set 
of structures
it is true in is in the ultrafilter.
-/
theorem sentence_realize (φ : L.Sentence) :
    (u : Filter α).Product M ⊨ φ ↔ ∀ᶠ a : α in u, M a ⊨ φ := by
  simp_rw [Sentence.Realize]
  rw [← realize_formula_cast φ, iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)

nonrec instance Product.instNonempty : Nonempty ((u : Filter α).Product M) :=
  letI : ∀ a, Inhabited (M a) := fun _ => Classical.inhabited_of_nonempty'
  inferInstance

end Ultraproduct

end Language

end FirstOrder

