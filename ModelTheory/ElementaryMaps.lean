/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.ModelTheory.Substructures

/-!
# Elementary Maps Between First-Order Structures

## Main Definitions

- A `FirstOrder.Language.ElementaryEmbedding` is an embedding that commutes with the
  realizations of formulas.
- The `FirstOrder.Language.elementaryDiagram` of a structure is the set of all sentences with
  parameters that the structure satisfies.
- `FirstOrder.Language.ElementaryEmbedding.ofModelsElementaryDiagram` is the canonical
  elementary embedding of any structure into a model of its elementary diagram.

## Main Results

- The Tarski-Vaught Test for embeddings: `FirstOrder.Language.Embedding.isElementary_of_exists`
  gives a simple criterion for an embedding to be elementary.
-/

@[expose] public section


open FirstOrder

namespace FirstOrder

namespace Language

open Structure

variable (L : Language) (M : Type*) (N : Type*) {P : Type*} {Q : Type*}
variable [L.Structure M] [L.Structure N] [L.Structure P] [L.Structure Q]

/-- An elementary embedding of first-order structures is an embedding that commutes with the
  realizations of formulas. -/
/-
**FirstOrder.Language.ElementaryEmbedding** 是 Mathlib 中的一个结构，位于命名空间 `FirstOrder.
Language`。
形式化陈述：ElementaryEmbedding where /-- The underlying embedding -/ toFun : M -> N -
- Porting note: -- The autoparam here used to be `obviously`. -- We have replace
d it with `aesop` but that isn't currently sufficient. -- See https://leanprover
.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Aesop.20and.20cases -- If th
at can be improved, we should remove the proofs below. map_formula' : forall ⦃n⦄
 (φ : L.Formula (Fin n)) (x : Fin n -> M), φ.Realize (toFun ∘ x) ↔ φ.Realize x
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An elementary embedding of first-order structures is an embedding that commutes 
with the
  realizations of formulas.
-/
structure ElementaryEmbedding where
  /-- The underlying embedding -/
  toFun : M → N
  -- Porting note:
  -- The autoparam here used to be `obviously`.
  -- We have replaced it with `aesop` but that isn't currently sufficient.
  -- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Aesop.20and.20cases
  -- If that can be improved, we should remove the proofs below.
  map_formula' :
    ∀ ⦃n⦄ (φ : L.Formula (Fin n)) (x : Fin n → M), φ.Realize (toFun ∘ x) ↔ φ.Realize x := by
    aesop

@[inherit_doc FirstOrder.Language.ElementaryEmbedding]
scoped[FirstOrder] notation:25 A " ↪ₑ[" L "] " B => FirstOrder.Language.ElementaryEmbedding L A B

variable {L} {M} {N}

namespace ElementaryEmbedding

attribute [coe] toFun

/-
**FirstOrder.Language.ElementaryEmbedding.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 
`FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：instFunLike : FunLike (M ↪ₑ[L] N) M N where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (M ↪ₑ[L] N) M N where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    simpa only [ElementaryEmbedding.mk.injEq]

@[simp]
/-
**FirstOrder.Language.ElementaryEmbedding.map_boundedFormula** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：map_boundedFormula (f : M ↪ₑ[L] N) {α : Type*} {n : Nat} (φ : L.BoundedFor
mula α n) (v : α -> M) (xs : Fin n -> M) : φ.Realize (f ∘ v) (f ∘ xs) ↔ φ.Realiz
e v xs
参数：f : M ↪ₑ[L] N；φ : L.BoundedFormula α n；v : α -> M；xs : Fin n -> M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_restrictFreeVar'`：realize_res
trictFreeVar' [DecidableEq α] {n : Nat} {φ : L.BoundedFormula α n} {s : Set α} (
h : ↑φ.freeVarFinset subseteq s) {v : α -> M} {xs…
· 使用定理 `Set.inclusion_eq_id`：inclusion_eq_id (h : s subseteq s) : inclusion h = 
id
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.map_formula'`：∀ {L : FirstOrder.
Language} {M : Type u_1} {N : Type u_2} [inst : L.Structure M] [inst_1 : L.Struc
ture N]   (self : L.ElementaryEmbedding M …
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Sum.elim_comp_inr`：∀ {α : Type u_1} {γ : Sort u_2} {β : Type u_3} (f : α
 → γ) (g : β → γ), Sum.elim f g ∘ Sum.inr = g
· 使用定理 `Sum.elim_comp_inl`：∀ {α : Type u_1} {γ : Sort u_2} {β : Type u_3} (f : α
 → γ) (g : β → γ), Sum.elim f g ∘ Sum.inl = f
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_restrictFreeVar`：realize_rest
rictFreeVar [DecidableEq α] {n : Nat} {φ : L.BoundedFormula α n} {f : φ.freeVarF
inset -> β} {v : β -> M} {xs : Fin n -> M} (v' :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_boundedFormula (f : M ↪ₑ[L] N) {α : Type*} {n : ℕ} (φ : L.BoundedFormula α n)
    (v : α → M) (xs : Fin n → M) : φ.Realize (f ∘ v) (f ∘ xs) ↔ φ.Realize v xs := by
  classical
    rw [← BoundedFormula.realize_restrictFreeVar' Set.Subset.rfl, Set.inclusion_eq_id]
    have h :=
      f.map_formula' ((φ.restrictFreeVar id).toFormula.relabel (Fintype.equivFin _))
        (Sum.elim (v ∘ (↑)) xs ∘ (Fintype.equivFin _).symm)
    simp only [Formula.realize_relabel, BoundedFormula.realize_toFormula] at h
    rw [← Function.comp_assoc _ _ (Fintype.equivFin _).symm,
      Function.comp_assoc _ (Fintype.equivFin _).symm (Fintype.equivFin _),
      _root_.Equiv.symm_comp_self, Function.comp_id, Function.comp_assoc, Sum.elim_comp_inl,
      Function.comp_assoc _ _ Sum.inr, Sum.elim_comp_inr, ← Function.comp_assoc] at h
    refine h.trans ?_
    rw [Function.comp_assoc _ _ (Fintype.equivFin _), _root_.Equiv.symm_comp_self,
      Function.comp_id, Sum.elim_comp_inl, Sum.elim_comp_inr (v ∘ Subtype.val) xs,
      BoundedFormula.realize_restrictFreeVar v (by simp)]

@[simp]
/-
**FirstOrder.Language.ElementaryEmbedding.map_formula** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：map_formula (f : M ↪ₑ[L] N) {α : Type*} (φ : L.Formula α) (x : α -> M) : φ
.Realize (f ∘ x) ↔ φ.Realize x
参数：f : M ↪ₑ[L] N；φ : L.Formula α；x : α -> M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Formula.Realize.eq_1`：∀ {L : FirstOrder.Language} {M
 : Type w} [inst : L.Structure M] {α : Type u'} (φ : L.Formula α) (v : α → M),  
 φ.Realize v = FirstOrder.Lang…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.map_boundedFormula`：map_boundedF
ormula (f : M ↪ₑ[L] N) {α : Type*} {n : Nat} (φ : L.BoundedFormula α n) (v : α -
> M) (xs : Fin n -> M) : φ.Realize (f ∘ v) (f ∘ …
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_formula (f : M ↪ₑ[L] N) {α : Type*} (φ : L.Formula α) (x : α → M) :
    φ.Realize (f ∘ x) ↔ φ.Realize x := by
  rw [Formula.Realize, Formula.Realize, ← f.map_boundedFormula, Unique.eq_default (f ∘ default)]
/-
**FirstOrder.Language.ElementaryEmbedding.map_sentence** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：map_sentence (f : M ↪ₑ[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ
参数：f : M ↪ₑ[L] N；φ : L.Sentence。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Sentence.Realize.eq_1`：∀ {L : FirstOrder.Language} (
M : Type w) [inst : L.Structure M] (φ : L.Sentence),   M ⊨ φ = FirstOrder.Langua
ge.Formula.Realize φ default
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.map_formula`：map_formula (f : M 
↪ₑ[L] N) {α : Type*} (φ : L.Formula α) (x : α -> M) : φ.Realize (f ∘ x) ↔ φ.Real
ize x
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_sentence (f : M ↪ₑ[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ := by
  rw [Sentence.Realize, Sentence.Realize, ← f.map_formula, Unique.eq_default (f ∘ default)]
/-
**FirstOrder.Language.ElementaryEmbedding.theory_model_iff** 是 Mathlib 中的一个定理，位于
命名空间 `FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：theory_model_iff (f : M ↪ₑ[L] N) (T : L.Theory) : M ⊨ T ↔ N ⊨ T
参数：f : M ↪ₑ[L] N；T : L.Theory。
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
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.map_sentence`：map_sentence (f : 
M ↪ₑ[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem theory_model_iff (f : M ↪ₑ[L] N) (T : L.Theory) : M ⊨ T ↔ N ⊨ T := by
  simp only [Theory.model_iff, f.map_sentence]
/-
**FirstOrder.Language.ElementaryEmbedding.elementarilyEquivalent** 是 Mathlib 中的一
个定理，位于命名空间 `FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：elementarilyEquivalent (f : M ↪ₑ[L] N) : M ≅[L] N
参数：f : M ↪ₑ[L] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.elementarilyEquivalent_iff`：elementarilyEquivalent_i
ff : M ≅[L] N ↔ forall φ : L.Sentence, M ⊨ φ ↔ N ⊨ φ
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.map_sentence`：map_sentence (f : 
M ↪ₑ[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ
-/
theorem elementarilyEquivalent (f : M ↪ₑ[L] N) : M ≅[L] N :=
  elementarilyEquivalent_iff.2 f.map_sentence

@[simp]
/-
**FirstOrder.Language.ElementaryEmbedding.injective** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.ElementaryEmbedding`。
形式化陈述：injective (φ : M ↪ₑ[L] N) : Function.Injective φ
参数：φ : M ↪ₑ[L] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.map_formula`：map_formula (f : M 
↪ₑ[L] N) {α : Type*} (φ : L.Formula α) (x : α -> M) : φ.Realize (f ∘ x) ↔ φ.Real
ize x
-/
theorem injective (φ : M ↪ₑ[L] N) : Function.Injective φ := by
  intro x y
  exact (φ.map_formula ((var 0).equal (var 1)) fun i => if i = 0 then x else y).1
/-
**FirstOrder.Language.ElementaryEmbedding.embeddingLike** 是 Mathlib 中的一个实例，位于命名空
间 `FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：embeddingLike : EmbeddingLike (M ↪ₑ[L] N) M N
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.injective`：injective (φ : M ↪ₑ[L
] N) : Function.Injective φ
-/
instance embeddingLike : EmbeddingLike (M ↪ₑ[L] N) M N :=
  { show FunLike (M ↪ₑ[L] N) M N from inferInstance with injective' := injective }

@[simp]
/-
**FirstOrder.Language.ElementaryEmbedding.map_fun** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.ElementaryEmbedding`。
形式化陈述：map_fun (φ : M ↪ₑ[L] N) {n : Nat} (f : L.Functions n) (x : Fin n -> M) : φ
 (funMap f x) = funMap f (φ ∘ x)
参数：φ : M ↪ₑ[L] N；f : L.Functions n；x : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.map_formula`：map_formula (f : M 
↪ₑ[L] N) {α : Type*} (φ : L.Formula α) (x : α -> M) : φ.Realize (f ∘ x) ↔ φ.Real
ize x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `FirstOrder.Language.Formula.realize_graph`：realize_graph {f : L.Function
s n} {x : Fin n -> M} {y : M} : (Formula.graph f).Realize (Fin.cons y x : _ -> M
) ↔ funMap f x = y
· 使用定理 `Fin.comp_cons`：comp_cons {α : Sort*} {β : Sort*} (g : α -> β) (y : α) (q
 : Fin n -> α) : g ∘ cons y q = cons (g y) (g ∘ q)
-/
theorem map_fun (φ : M ↪ₑ[L] N) {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    φ (funMap f x) = funMap f (φ ∘ x) := by
  have h := φ.map_formula (Formula.graph f) (Fin.cons (funMap f x) x)
  rw [Formula.realize_graph, Fin.comp_cons, Formula.realize_graph] at h
  rw [eq_comm, h]

@[simp]
/-
**FirstOrder.Language.ElementaryEmbedding.map_rel** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.ElementaryEmbedding`。
形式化陈述：map_rel (φ : M ↪ₑ[L] N) {n : Nat} (r : L.Relations n) (x : Fin n -> M) : R
elMap r (φ ∘ x) ↔ RelMap r x
参数：φ : M ↪ₑ[L] N；r : L.Relations n；x : Fin n -> M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.map_formula`：map_formula (f : M 
↪ₑ[L] N) {α : Type*} (φ : L.Formula α) (x : α -> M) : φ.Realize (f ∘ x) ↔ φ.Real
ize x
-/
theorem map_rel (φ : M ↪ₑ[L] N) {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    RelMap r (φ ∘ x) ↔ RelMap r x :=
  haveI h := φ.map_formula (r.formula var) x
  h
/-
**FirstOrder.Language.ElementaryEmbedding.strongHomClass** 是 Mathlib 中的一个实例，位于命名
空间 `FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：strongHomClass : StrongHomClass L (M ↪ₑ[L] N) M N where map_fun
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.map_fun`：map_fun (φ : M ↪ₑ[L] N)
 {n : Nat} (f : L.Functions n) (x : Fin n -> M) : φ (funMap f x) = funMap f (φ ∘
 x)
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.map_rel`：map_rel (φ : M ↪ₑ[L] N)
 {n : Nat} (r : L.Relations n) (x : Fin n -> M) : RelMap r (φ ∘ x) ↔ RelMap r x
-/
instance strongHomClass : StrongHomClass L (M ↪ₑ[L] N) M N where
  map_fun := map_fun
  map_rel := map_rel

@[simp]
/-
**FirstOrder.Language.ElementaryEmbedding.map_constants** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：map_constants (φ : M ↪ₑ[L] N) (c : L.Constants) : φ c = c
参数：φ : M ↪ₑ[L] N；c : L.Constants。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.HomClass.map_constants`：∀ {L : FirstOrder.Language} 
{F : Type u_3} {M : Type u_4} {N : Type u_5} [inst : L.Structure M] [inst_1 : L.
Structure N]   [inst_2 : FunLike…
· 使用定理 `FirstOrder.Language.StrongHomClass.homClass`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N] {F :
 Type u_3}   [inst_2 : FunLike F …
-/
theorem map_constants (φ : M ↪ₑ[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c

/-- An elementary embedding is also a first-order embedding. -/
/-
**FirstOrder.Language.ElementaryEmbedding.toEmbedding** 是 Mathlib 中的一个定义，位于命名空间 
`FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：toEmbedding (f : M ↪ₑ[L] N) : M ↪[L] N where toFun
参数：f : M ↪ₑ[L] N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.injective`：injective (φ : M ↪ₑ[L
] N) : Function.Injective φ

--- 原说明 ---
An elementary embedding is also a first-order embedding.
-/
def toEmbedding (f : M ↪ₑ[L] N) : M ↪[L] N where
  toFun := f
  inj' := f.injective
  map_fun' {_} f x := by simp
  map_rel' {_} R x := by simp

/-- An elementary embedding is also a first-order homomorphism. -/
/-
**FirstOrder.Language.ElementaryEmbedding.toHom** 是 Mathlib 中的一个定义，位于命名空间 `First
Order.Language.ElementaryEmbedding`。
形式化陈述：toHom (f : M ↪ₑ[L] N) : M ->[L] N where toFun
参数：f : M ↪ₑ[L] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An elementary embedding is also a first-order homomorphism.
-/
def toHom (f : M ↪ₑ[L] N) : M →[L] N where
  toFun := f
  map_fun' {_} f x := by simp
  map_rel' {_} R x := by simp

@[simp]
/-
**FirstOrder.Language.ElementaryEmbedding.toEmbedding_toHom** 是 Mathlib 中的一个定理，位
于命名空间 `FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：toEmbedding_toHom (f : M ↪ₑ[L] N) : f.toEmbedding.toHom = f.toHom
参数：f : M ↪ₑ[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEmbedding_toHom (f : M ↪ₑ[L] N) : f.toEmbedding.toHom = f.toHom :=
  rfl

@[simp]
/-
**FirstOrder.Language.ElementaryEmbedding.coe_toHom** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.ElementaryEmbedding`。
形式化陈述：coe_toHom {f : M ↪ₑ[L] N} : (f.toHom : M -> N) = (f : M -> N)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toHom {f : M ↪ₑ[L] N} : (f.toHom : M → N) = (f : M → N) :=
  rfl

@[simp]
/-
**FirstOrder.Language.ElementaryEmbedding.coe_toEmbedding** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：coe_toEmbedding (f : M ↪ₑ[L] N) : (f.toEmbedding : M -> N) = (f : M -> N)
参数：f : M ↪ₑ[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEmbedding (f : M ↪ₑ[L] N) : (f.toEmbedding : M → N) = (f : M → N) :=
  rfl
/-
**FirstOrder.Language.ElementaryEmbedding.coe_injective** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：coe_injective : @Function.Injective (M ↪ₑ[L] N) (M -> N) (↑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_injective : @Function.Injective (M ↪ₑ[L] N) (M → N) (↑) :=
  DFunLike.coe_injective

@[ext]
/-
**FirstOrder.Language.ElementaryEmbedding.ext** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.ElementaryEmbedding`。
形式化陈述：ext ⦃f g : M ↪ₑ[L] N⦄ (h : forall x, f x = g x) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext ⦃f g : M ↪ₑ[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

variable (L) (M)

/-- The identity elementary embedding from a structure to itself -/
@[refl]
/-
**FirstOrder.Language.ElementaryEmbedding.refl** 是 Mathlib 中的一个定义，位于命名空间 `FirstO
rder.Language.ElementaryEmbedding`。
形式化陈述：refl : M ↪ₑ[L] M where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity elementary embedding from a structure to itself
-/
def refl : M ↪ₑ[L] M where toFun := id

variable {L} {M}
/-
**FirstOrder.Language.ElementaryEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder
.Language.ElementaryEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (M ↪ₑ[L] M) :=
  ⟨refl L M⟩

@[simp]
/-
**FirstOrder.Language.ElementaryEmbedding.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：refl_apply (x : M) : refl L M x = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_apply (x : M) : refl L M x = x :=
  rfl

/-- Composition of elementary embeddings -/
@[trans]
/-
**FirstOrder.Language.ElementaryEmbedding.comp** 是 Mathlib 中的一个定义，位于命名空间 `FirstO
rder.Language.ElementaryEmbedding`。
形式化陈述：comp (hnp : N ↪ₑ[L] P) (hmn : M ↪ₑ[L] N) : M ↪ₑ[L] P where toFun
参数：hnp : N ↪ₑ[L] P；hmn : M ↪ₑ[L] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of elementary embeddings
-/
def comp (hnp : N ↪ₑ[L] P) (hmn : M ↪ₑ[L] N) : M ↪ₑ[L] P where
  toFun := hnp ∘ hmn
  map_formula' n φ x := by simp [Function.comp_assoc]

@[simp]
/-
**FirstOrder.Language.ElementaryEmbedding.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：comp_apply (g : N ↪ₑ[L] P) (f : M ↪ₑ[L] N) (x : M) : g.comp f x = g (f x)
参数：g : N ↪ₑ[L] P；f : M ↪ₑ[L] N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (g : N ↪ₑ[L] P) (f : M ↪ₑ[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/-- Composition of elementary embeddings is associative. -/
/-
**FirstOrder.Language.ElementaryEmbedding.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：comp_assoc (f : M ↪ₑ[L] N) (g : N ↪ₑ[L] P) (h : P ↪ₑ[L] Q) : (h.comp g).co
mp f = h.comp (g.comp f)
参数：f : M ↪ₑ[L] N；g : N ↪ₑ[L] P；h : P ↪ₑ[L] Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of elementary embeddings is associative.
-/
theorem comp_assoc (f : M ↪ₑ[L] N) (g : N ↪ₑ[L] P) (h : P ↪ₑ[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

/-- Lifts an elementary embedding to the expanded language with constants -/
/-
**FirstOrder.Language.ElementaryEmbedding.liftWithConstants** 是 Mathlib 中的一个定义，位
于命名空间 `FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：liftWithConstants (f : M ↪ₑ[L] N) (A : Set M) : M ↪ₑ[L[[A]]] (f.toEmbeddin
g.withConstants A)
参数：f : M ↪ₑ[L] N；A : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifts an elementary embedding to the expanded language with constants
-/
def liftWithConstants (f : M ↪ₑ[L] N) (A : Set M) :
    M ↪ₑ[L[[A]]] (f.toEmbedding.withConstants A) := by
  refine ⟨f, ?_⟩
  intro n φ x
  have h :
    (Sum.elim (fun a ↦ ↑(L.con a)) (⇑f ∘ x) :
      ↑A ⊕ Fin n → f.toEmbedding.withConstants A) =
    f ∘ Sum.elim (fun a ↦ ↑(L.con a)) x :=
    (Sum.comp_elim _ _ _).symm
  simpa only [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv, h] using!
    f.map_formula
      (BoundedFormula.constantsVarsEquiv φ)
      (Sum.elim (fun a ↦ ↑(L.con a)) x)

end ElementaryEmbedding

variable (L) (M)

/-- The elementary diagram of an `L`-structure is the set of all sentences with parameters it
  satisfies. -/
/-
**FirstOrder.Language.elementaryDiagram** 是 Mathlib 中的一个缩写定义，位于命名空间 `FirstOrder.
Language`。
形式化陈述：elementaryDiagram : L[[M]].Theory
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The elementary diagram of an `L`-structure is the set of all sentences with para
meters it
  satisfies.
-/
abbrev elementaryDiagram : L[[M]].Theory :=
  L[[M]].completeTheory M

set_option backward.isDefEq.respectTransparency false in
/-- The canonical elementary embedding of an `L`-structure into any model of its elementary diagram
-/
@[simps]
/-
**FirstOrder.Language.ElementaryEmbedding.ofModelsElementaryDiagram** 是 Mathlib 
中的一个定义，位于命名空间 `FirstOrder.Language.ElementaryEmbedding`。
形式化陈述：(L : FirstOrder.Language) →   (M : Type u_1) →     [inst : L.Structure M] 
→       (N : Type u_5) →         [inst_1 : L.Structure N] →           [inst_2 : 
(L.withConstants M).Structure N] →             [(L.lhomWithConstants M).IsExpans
ionOn N] → [N ⊨ L.elementaryDiagram M] → L.ElementaryEmbedding M N
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical elementary embedding of an `L`-structure into any model of its ele
mentary diagram
-/
def ElementaryEmbedding.ofModelsElementaryDiagram (N : Type*) [L.Structure N] [L[[M]].Structure N]
    [(lhomWithConstants L M).IsExpansionOn N] [N ⊨ L.elementaryDiagram M] : M ↪ₑ[L] N :=
  ⟨((↑) : L[[M]].Constants → N) ∘ Sum.inr, fun n φ x => by
    refine
      _root_.trans ?_
        ((realize_iff_of_model_completeTheory M N
              (((L.lhomWithConstants M).onBoundedFormula φ).subst
                  (Constants.term ∘ Sum.inr ∘ x)).alls).trans
          ?_)
    · simp_rw [Sentence.Realize, BoundedFormula.realize_alls, BoundedFormula.realize_subst,
        LHom.realize_onBoundedFormula, Formula.Realize, Unique.forall_iff, Function.comp_def,
        Term.realize_constants]
    · simp_rw [Sentence.Realize, BoundedFormula.realize_alls, BoundedFormula.realize_subst,
        LHom.realize_onBoundedFormula, Formula.Realize, Unique.forall_iff]
      rfl⟩

variable {L M}

namespace Embedding

/-- The **Tarski-Vaught test** for elementarity of an embedding. -/
/-
**FirstOrder.Language.Embedding.isElementary_of_exists** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.Embedding`。
形式化陈述：isElementary_of_exists (f : M ↪[L] N) (htv : forall (n : Nat) (φ : L.Bound
edFormula Empty (n + 1)) (x : Fin n -> M) (a : N), φ.Realize default (Fin.snoc (
f ∘ x) a : _ -> N) -> exists b : M, φ.Realize default (Fin.snoc (f ∘ x) (f b) : 
_ -> N)) : forall {n} (φ : L.Formula (Fin n)) (x : Fin n -> M), φ.Realize (f ∘ x
) ↔ φ.Realize x
参数：f : M ↪[L] N；htv : forall (n : Nat) (φ : L.BoundedFormula Empty (n + 1)) (x :
 Fin n -> M) (a : N), φ.Realize default (Fin.snoc (f ∘ x) a : _ -> N) -> exists 
b : M, φ.Realize default (Fin.snoc (f ∘ x) (f b) : _ -> N)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FirstOrder.Language.HomClass.realize_term`：∀ {L : FirstOrder.Language} {
M : Type w} {N : Type u_1} [inst : L.Structure M] [inst_1 : L.Structure N] {α : 
Type u'}   {F : Type u_4} [inst…
· 使用定理 `FirstOrder.Language.StrongHomClass.homClass`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N] {F :
 Type u_3}   [inst_2 : FunLike F …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `FirstOrder.Language.Embedding.map_rel`：map_rel (φ : M ↪[L] N) {n : Nat} 
(r : L.Relations n) (x : Fin n -> M) : RelMap r (φ ∘ x) ↔ RelMap r x
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Fin.comp_snoc`：comp_snoc {α : Sort*} {β : Sort*} (g : α -> β) (q : Fin n
 -> α) (y : α) : g ∘ snoc q y = snoc (g ∘ q) (g y)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_not`：realize_not : φ.not.Real
ize v xs ↔ ¬φ.Realize v xs
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `FirstOrder.Language.Formula.realize_relabel_sumInr`：realize_relabel_sumI
nr (φ : L.Formula (Fin n)) {v : Empty -> M} {x : Fin n -> M} : (BoundedFormula.r
elabel Sum.inr φ).Realize v x ↔ φ.Realiz…
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r

--- 原说明 ---
The **Tarski-Vaught test** for elementarity of an embedding.
-/
theorem isElementary_of_exists (f : M ↪[L] N)
    (htv :
      ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → M) (a : N),
        φ.Realize default (Fin.snoc (f ∘ x) a : _ → N) →
          ∃ b : M, φ.Realize default (Fin.snoc (f ∘ x) (f b) : _ → N)) :
    ∀ {n} (φ : L.Formula (Fin n)) (x : Fin n → M), φ.Realize (f ∘ x) ↔ φ.Realize x := by
  suffices h : ∀ (n : ℕ) (φ : L.BoundedFormula Empty n) (xs : Fin n → M),
      φ.Realize (f ∘ default) (f ∘ xs) ↔ φ.Realize default xs by
    intro n φ x
    exact φ.realize_relabel_sumInr.symm.trans (_root_.trans (h n _ _) φ.realize_relabel_sumInr)
  refine fun n φ => φ.recOn ?_ ?_ ?_ ?_ ?_
  · exact fun {_} _ => Iff.rfl
  · intros
    simp [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term]
  · intro _ _ R ts xs
    simp only [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term]
    simp_rw [← Function.comp_apply (f := (f : M → N)),
      ← Function.comp_apply (f := Term.realize (Sum.elim default xs)),
      ← Function.comp_apply (f := (f : M → N) ∘ Term.realize (Sum.elim default xs))]
    rw [Function.comp_assoc, map_rel f]
  · intro _ _ _ ih1 ih2 _
    simp [ih1, ih2]
  · intro n φ ih xs
    simp only [BoundedFormula.realize_all]
    refine ⟨fun h a => ?_, ?_⟩
    · rw [← ih, Fin.comp_snoc]
      exact h (f a)
    · contrapose!
      rintro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := htv n φ.not xs a (by
          rw [BoundedFormula.realize_not, ← Unique.eq_default (f ∘ default)]
          exact ha)
      refine ⟨b, fun h => hb (Eq.mp ?_ ((ih _).2 h))⟩
      rw [Unique.eq_default (f ∘ default), Fin.comp_snoc]

/-- Bundles an embedding satisfying the Tarski-Vaught test as an elementary embedding. -/
@[simps]
/-
**FirstOrder.Language.Embedding.toElementaryEmbedding** 是 Mathlib 中的一个定义，位于命名空间 
`FirstOrder.Language.Embedding`。
形式化陈述：toElementaryEmbedding (f : M ↪[L] N) (htv : forall (n : Nat) (φ : L.Bounde
dFormula Empty (n + 1)) (x : Fin n -> M) (a : N), φ.Realize default (Fin.snoc (f
 ∘ x) a : _ -> N) -> exists b : M, φ.Realize default (Fin.snoc (f ∘ x) (f b) : _
 -> N)) : M ↪ₑ[L] N
参数：f : M ↪[L] N；htv : forall (n : Nat) (φ : L.BoundedFormula Empty (n + 1)) (x :
 Fin n -> M) (a : N), φ.Realize default (Fin.snoc (f ∘ x) a : _ -> N) -> exists 
b : M, φ.Realize default (Fin.snoc (f ∘ x) (f b) : _ -> N)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Embedding.isElementary_of_exists`：isElementary_of_ex
ists (f : M ↪[L] N) (htv : forall (n : Nat) (φ : L.BoundedFormula Empty (n + 1))
 (x : Fin n -> M) (a : N), φ.Realize defau…

--- 原说明 ---
Bundles an embedding satisfying the Tarski-Vaught test as an elementary embeddin
g.
-/
def toElementaryEmbedding (f : M ↪[L] N)
    (htv :
      ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → M) (a : N),
        φ.Realize default (Fin.snoc (f ∘ x) a : _ → N) →
          ∃ b : M, φ.Realize default (Fin.snoc (f ∘ x) (f b) : _ → N)) :
    M ↪ₑ[L] N :=
  ⟨f, fun _ => f.isElementary_of_exists htv⟩

end Embedding

namespace Equiv

/-- A first-order equivalence is also an elementary embedding. -/
/-
**FirstOrder.Language.Equiv.toElementaryEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Fir
stOrder.Language.Equiv`。
形式化陈述：toElementaryEmbedding (f : M ≃[L] N) : M ↪ₑ[L] N where toFun
参数：f : M ≃[L] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A first-order equivalence is also an elementary embedding.
-/
def toElementaryEmbedding (f : M ≃[L] N) : M ↪ₑ[L] N where
  toFun := f

@[simp]
/-
**FirstOrder.Language.Equiv.toElementaryEmbedding_toEmbedding** 是 Mathlib 中的一个定理
，位于命名空间 `FirstOrder.Language.Equiv`。
形式化陈述：toElementaryEmbedding_toEmbedding (f : M ≃[L] N) : f.toElementaryEmbedding
.toEmbedding = f.toEmbedding
参数：f : M ≃[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toElementaryEmbedding_toEmbedding (f : M ≃[L] N) :
    f.toElementaryEmbedding.toEmbedding = f.toEmbedding :=
  rfl

@[simp]
/-
**FirstOrder.Language.Equiv.coe_toElementaryEmbedding** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.Equiv`。
形式化陈述：coe_toElementaryEmbedding (f : M ≃[L] N) : (f.toElementaryEmbedding : M ->
 N) = (f : M -> N)
参数：f : M ≃[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toElementaryEmbedding (f : M ≃[L] N) :
    (f.toElementaryEmbedding : M → N) = (f : M → N) :=
  rfl

end Equiv

@[simp]
/-
**FirstOrder.Language.realize_term_substructure** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language`。
形式化陈述：realize_term_substructure {α : Type*} {S : L.Substructure M} (v : α -> S) 
(t : L.Term α) : t.realize ((↑) ∘ v) = (↑(t.realize v) : M)
参数：v : α -> S；t : L.Term α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.HomClass.realize_term`：∀ {L : FirstOrder.Language} {
M : Type w} {N : Type u_1} [inst : L.Structure M] [inst_1 : L.Structure N] {α : 
Type u'}   {F : Type u_4} [inst…
· 使用定理 `FirstOrder.Language.StrongHomClass.homClass`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N] {F :
 Type u_3}   [inst_2 : FunLike F …
-/
theorem realize_term_substructure {α : Type*} {S : L.Substructure M} (v : α → S) (t : L.Term α) :
    t.realize ((↑) ∘ v) = (↑(t.realize v) : M) :=
  HomClass.realize_term S.subtype

end Language

end FirstOrder

