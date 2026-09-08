/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.Satisfiability

/-!
# Type Spaces

This file defines the space of complete types over a first-order theory.
(Note that types in model theory are different from types in type theory.)

## Main Definitions

- `FirstOrder.Language.Theory.CompleteType`:
  `T.CompleteType α` consists of complete types over the theory `T` with variables `α`.
- `FirstOrder.Language.Theory.typeOf` is the type of a given tuple.
- `FirstOrder.Language.Theory.realizedTypes`: `T.realizedTypes M α` is the set of
  types in `T.CompleteType α` that are realized in `M` - that is, the type of some tuple in `M`.

## Main Results

- `FirstOrder.Language.Theory.CompleteType.nonempty_iff`:
  The space `T.CompleteType α` is nonempty exactly when `T` is satisfiable.
- `FirstOrder.Language.Theory.CompleteType.exists_modelType_is_realized_in`: Every type is realized
  in some model.

## Implementation Notes

- Complete types are implemented as maximal consistent theories in an expanded language.
  More frequently they are described as maximal consistent sets of formulas, but this is equivalent.

## TODO

- Connect `T.CompleteType α` to sets of formulas `L.Formula α`.
-/

@[expose] public section



universe u v w w'

open Cardinal Set FirstOrder

namespace FirstOrder

namespace Language

namespace Theory

variable {L : Language.{u, v}} (T : L.Theory) (α : Type w)

/-- A complete type over a given theory in a certain type of variables is a maximally
  consistent (with the theory) set of formulas in that type. -/
/-
**FirstOrder.Language.Theory.CompleteType** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrde
r.Language.Theory`。
形式化陈述：{L : FirstOrder.Language} → L.Theory → Type w → Type (max (max u v) w)
参数：max (max u v) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete type over a given theory in a certain type of variables is a maximall
y
  consistent (with the theory) set of formulas in that type.
-/
structure CompleteType where
  /-- The underlying theory -/
  toTheory : L[[α]].Theory
  subset' : (L.lhomWithConstants α).onTheory T ⊆ toTheory
  isMaximal' : toTheory.IsMaximal

variable {α}

/-- The clopen set of complete types which contain a formula. -/
/-
**FirstOrder.Language.Theory.typesWith** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lan
guage.Theory`。
形式化陈述：typesWith (T : L.Theory) : L[[α]].Sentence -> Set (CompleteType T α)
参数：T : L.Theory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The clopen set of complete types which contain a formula.
-/
def typesWith (T : L.Theory) : L[[α]].Sentence → Set (CompleteType T α) :=
  fun φ ↦ {p | φ ∈ p.toTheory}

variable {T}

namespace CompleteType

attribute [coe] CompleteType.toTheory

/-
**FirstOrder.Language.Theory.CompleteType.Sentence.instSetLike** 是 Mathlib 中的一个定
义，位于命名空间 `FirstOrder.Language.Theory.CompleteType.Sentence`。
形式化陈述：{L : FirstOrder.Language} → {T : L.Theory} → {α : Type w} → SetLike (T.Com
pleteType α) (L.withConstants α).Sentence
参数：T.CompleteType α；L.withConstants α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Sentence.instSetLike : SetLike (T.CompleteType α) L[[α]].Sentence :=
  ⟨fun p => p.toTheory, fun p q h => by
    cases p
    cases q
    congr ⟩
/-
**FirstOrder.Language.Theory.CompleteType.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder
.Language.Theory.CompleteType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (T.CompleteType α) := .ofSetLike (T.CompleteType α) (L[[α]].Sentence)
/-
**FirstOrder.Language.Theory.CompleteType.isMaximal** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.Theory.CompleteType`。
形式化陈述：isMaximal (p : T.CompleteType α) : IsMaximal (p : L[[α]].Theory)
参数：p : T.CompleteType α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.CompleteType.isMaximal'`：∀ {L : FirstOrder.La
nguage} {T : L.Theory} {α : Type w} (self : T.CompleteType α), (↑self).IsMaximal
-/
theorem isMaximal (p : T.CompleteType α) : IsMaximal (p : L[[α]].Theory) :=
  p.isMaximal'
/-
**FirstOrder.Language.Theory.CompleteType.subset** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Theory.CompleteType`。
形式化陈述：subset (p : T.CompleteType α) : (L.lhomWithConstants α).onTheory T subsete
q (p : L[[α]].Theory)
参数：p : T.CompleteType α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.CompleteType.subset'`：∀ {L : FirstOrder.Langu
age} {T : L.Theory} {α : Type w} (self : T.CompleteType α),   (L.lhomWithConstan
ts α).onTheory T ⊆ ↑self
-/
theorem subset (p : T.CompleteType α) : (L.lhomWithConstants α).onTheory T ⊆ (p : L[[α]].Theory) :=
  p.subset'
/-
**FirstOrder.Language.Theory.CompleteType.mem_or_not_mem** 是 Mathlib 中的一个定理，位于命名
空间 `FirstOrder.Language.Theory.CompleteType`。
形式化陈述：mem_or_not_mem (p : T.CompleteType α) (φ : L[[α]].Sentence) : φ in p ∨ φ.n
ot in p
参数：p : T.CompleteType α；φ : L[[α]].Sentence。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.IsMaximal.mem_or_not_mem`：∀ {L : FirstOrder.L
anguage} {T : L.Theory},   T.IsMaximal → ∀ (φ : L.Sentence), φ ∈ T ∨ FirstOrder.
Language.Formula.not φ ∈ T
· 使用定理 `FirstOrder.Language.Theory.CompleteType.isMaximal`：isMaximal (p : T.Comp
leteType α) : IsMaximal (p : L[[α]].Theory)
-/
theorem mem_or_not_mem (p : T.CompleteType α) (φ : L[[α]].Sentence) : φ ∈ p ∨ φ.not ∈ p :=
  p.isMaximal.mem_or_not_mem φ
/-
**FirstOrder.Language.Theory.CompleteType.false_of_mem_of_not_mem** 是 Mathlib 中的
一个引理，位于命名空间 `FirstOrder.Language.Theory.CompleteType`。
形式化陈述：false_of_mem_of_not_mem (hT : T.IsSatisfiable) {φ : L.Sentence} (hφ : φ in
 T) (hφ' : ∼φ in T) : False
参数：hT : T.IsSatisfiable；hφ : φ in T；hφ' : ∼φ in T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.Model.realize_of_mem`：∀ {L : FirstOrder.Langu
age} {M : Type w} {inst : L.Structure M} {T : L.Theory} [self : M ⊨ T], ∀ φ ∈ T,
 M ⊨ φ
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
-/
lemma false_of_mem_of_not_mem (hT : T.IsSatisfiable) {φ : L.Sentence} (hφ : φ ∈ T) (hφ' : ∼φ ∈ T) :
    False :=
  have ⟨M⟩ := hT
  (M.is_model.realize_of_mem _ hφ') (M.is_model.realize_of_mem _ hφ)
/-
**FirstOrder.Language.Theory.CompleteType.mem_of_models** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.Theory.CompleteType`。
形式化陈述：mem_of_models (p : T.CompleteType α) {φ : L[[α]].Sentence} (h : (L.lhomWit
hConstants α).onTheory T ⊨ᵇ φ) : φ in p
参数：p : T.CompleteType α；h : (L.lhomWithConstants α).onTheory T ⊨ᵇ φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `FirstOrder.Language.Theory.CompleteType.mem_or_not_mem`：mem_or_not_mem (
p : T.CompleteType α) (φ : L[[α]].Sentence) : φ in p ∨ φ.not in p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Theory.models_iff_not_satisfiable`：models_iff_not_sa
tisfiable (φ : L.Sentence) : T ⊨ᵇ φ ↔ ¬IsSatisfiable (T union {φ.not})
· 使用定理 `FirstOrder.Language.Theory.IsSatisfiable.mono`：∀ {L : FirstOrder.Languag
e} {T T' : L.Theory}, T'.IsSatisfiable → T ⊆ T' → T.IsSatisfiable
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `FirstOrder.Language.Theory.CompleteType.isMaximal`：isMaximal (p : T.Comp
leteType α) : IsMaximal (p : L[[α]].Theory)
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `FirstOrder.Language.Theory.CompleteType.subset`：subset (p : T.CompleteTy
pe α) : (L.lhomWithConstants α).onTheory T subseteq (p : L[[α]].Theory)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem mem_of_models (p : T.CompleteType α) {φ : L[[α]].Sentence}
    (h : (L.lhomWithConstants α).onTheory T ⊨ᵇ φ) : φ ∈ p :=
  (p.mem_or_not_mem φ).resolve_right fun con =>
    ((models_iff_not_satisfiable _).1 h)
      (p.isMaximal.1.mono (union_subset p.subset (singleton_subset_iff.2 con)))
/-
**FirstOrder.Language.Theory.CompleteType.not_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.Theory.CompleteType`。
形式化陈述：not_mem_iff (p : T.CompleteType α) (φ : L[[α]].Sentence) : φ.not in p ↔ φ 
∉ p
参数：p : T.CompleteType α；φ : L[[α]].Sentence。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `FirstOrder.Language.Theory.IsSatisfiable.mono`：∀ {L : FirstOrder.Languag
e} {T T' : L.Theory}, T'.IsSatisfiable → T ⊆ T' → T.IsSatisfiable
· 使用定理 `FirstOrder.Language.Theory.CompleteType.isMaximal`：isMaximal (p : T.Comp
leteType α) : IsMaximal (p : L[[α]].Theory)
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `FirstOrder.Language.Theory.CompleteType.mem_or_not_mem`：mem_or_not_mem (
p : T.CompleteType α) (φ : L[[α]].Sentence) : φ in p ∨ φ.not in p
-/
theorem not_mem_iff (p : T.CompleteType α) (φ : L[[α]].Sentence) : φ.not ∈ p ↔ φ ∉ p :=
  ⟨fun hf ht => by
    have h : ¬IsSatisfiable ({φ, φ.not} : L[[α]].Theory) := by
      rintro ⟨@⟨_, _, h, _⟩⟩
      simp only [model_iff, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq] at h
      exact h.2 h.1
    refine h (p.isMaximal.1.mono ?_)
    rw [insert_subset_iff, singleton_subset_iff]
    exact ⟨ht, hf⟩, (p.mem_or_not_mem φ).resolve_left⟩

@[simp]
/-
**FirstOrder.Language.Theory.CompleteType.compl_setOfPred_mem** 是 Mathlib 中的一个定理
，位于命名空间 `FirstOrder.Language.Theory.CompleteType`。
形式化陈述：compl_setOfPred_mem {φ : L[[α]].Sentence} : { p : T.CompleteType α | φ in 
p }ᶜ = { p : T.CompleteType α | φ.not in p }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `FirstOrder.Language.Theory.CompleteType.not_mem_iff`：not_mem_iff (p : T.
CompleteType α) (φ : L[[α]].Sentence) : φ.not in p ↔ φ ∉ p
-/
theorem compl_setOfPred_mem {φ : L[[α]].Sentence} :
    { p : T.CompleteType α | φ ∈ p }ᶜ = { p : T.CompleteType α | φ.not ∈ p } :=
  ext fun _ => (not_mem_iff _ _).symm

@[deprecated (since := "2026-07-09")] alias compl_setOf_mem := compl_setOfPred_mem
/-
**FirstOrder.Language.Theory.CompleteType.setOfPred_subset_eq_empty_iff** 是 Math
lib 中的一个定理，位于命名空间 `FirstOrder.Language.Theory.CompleteType`。
形式化陈述：setOfPred_subset_eq_empty_iff (S : L[[α]].Theory) : { p : T.CompleteType α
 | S subseteq ↑p } = ∅ ↔ ¬((L.lhomWithConstants α).onTheory T union S).IsSatisfi
able
参数：S : L[[α]].Theory。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_not_comm`：iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Set.Nonempty.eq_1`：∀ {α : Type u} (s : Set α), s.Nonempty = ∃ x, x ∈ s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `FirstOrder.Language.Theory.completeTheory.subset`：∀ {L : FirstOrder.Lang
uage} {M : Type w} [inst : L.Structure M] {T : L.Theory} [MT : M ⊨ T], T ⊆ L.com
pleteTheory M
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
· 使用定理 `FirstOrder.Language.completeTheory.isMaximal`：isMaximal [Nonempty M] : (
L.completeTheory M).IsMaximal
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `FirstOrder.Language.Theory.IsSatisfiable.mono`：∀ {L : FirstOrder.Languag
e} {T T' : L.Theory}, T'.IsSatisfiable → T ⊆ T' → T.IsSatisfiable
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `FirstOrder.Language.Theory.CompleteType.isMaximal`：isMaximal (p : T.Comp
leteType α) : IsMaximal (p : L[[α]].Theory)
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `FirstOrder.Language.Theory.CompleteType.subset`：subset (p : T.CompleteTy
pe α) : (L.lhomWithConstants α).onTheory T subseteq (p : L[[α]].Theory)
-/
theorem setOfPred_subset_eq_empty_iff (S : L[[α]].Theory) :
    { p : T.CompleteType α | S ⊆ ↑p } = ∅ ↔
      ¬((L.lhomWithConstants α).onTheory T ∪ S).IsSatisfiable := by
  rw [iff_not_comm, ← not_nonempty_iff_eq_empty, Classical.not_not, Set.Nonempty]
  refine
    ⟨fun h =>
      ⟨⟨L[[α]].completeTheory h.some, (subset_union_left (t := S)).trans completeTheory.subset,
          completeTheory.isMaximal L[[α]] h.some⟩,
        (((L.lhomWithConstants α).onTheory T).subset_union_right).trans completeTheory.subset⟩,
      ?_⟩
  rintro ⟨p, hp⟩
  exact p.isMaximal.1.mono (union_subset p.subset hp)

@[deprecated (since := "2026-07-09")]
alias setOf_subset_eq_empty_iff := setOfPred_subset_eq_empty_iff
/-
**FirstOrder.Language.Theory.CompleteType.setOfPred_mem_eq_univ_iff** 是 Mathlib 
中的一个定理，位于命名空间 `FirstOrder.Language.Theory.CompleteType`。
形式化陈述：setOfPred_mem_eq_univ_iff (φ : L[[α]].Sentence) : { p : T.CompleteType α |
 φ in p } = Set.univ ↔ (L.lhomWithConstants α).onTheory T ⊨ᵇ φ
参数：φ : L[[α]].Sentence。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Theory.models_iff_not_satisfiable`：models_iff_not_sa
tisfiable (φ : L.Sentence) : T ⊨ᵇ φ ↔ ¬IsSatisfiable (T union {φ.not})
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_empty_iff`：compl_empty_iff {s : Set α} : sᶜ = ∅ ↔ s = univ
· 使用定理 `FirstOrder.Language.Theory.CompleteType.compl_setOfPred_mem`：compl_setOf
Pred_mem {φ : L[[α]].Sentence} : { p : T.CompleteType α | φ in p }ᶜ = { p : T.Co
mpleteType α | φ.not in p }
· 使用定理 `FirstOrder.Language.Theory.CompleteType.setOfPred_subset_eq_empty_iff`：s
etOfPred_subset_eq_empty_iff (S : L[[α]].Theory) : { p : T.CompleteType α | S su
bseteq ↑p } = ∅ ↔ ¬((L.lhomWithConstants α).onTheory T unio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem setOfPred_mem_eq_univ_iff (φ : L[[α]].Sentence) :
    { p : T.CompleteType α | φ ∈ p } = Set.univ ↔ (L.lhomWithConstants α).onTheory T ⊨ᵇ φ := by
  rw [models_iff_not_satisfiable, ← compl_empty_iff, compl_setOfPred_mem,
    ← setOfPred_subset_eq_empty_iff]
  simp

@[deprecated (since := "2026-07-09")] alias setOf_mem_eq_univ_iff := setOfPred_mem_eq_univ_iff
/-
**FirstOrder.Language.Theory.CompleteType.setOfPred_subset_eq_univ_iff** 是 Mathl
ib 中的一个定理，位于命名空间 `FirstOrder.Language.Theory.CompleteType`。
形式化陈述：setOfPred_subset_eq_univ_iff (S : L[[α]].Theory) : { p : T.CompleteType α 
| S subseteq ↑p } = Set.univ ↔ forall φ, φ in S -> (L.lhomWithConstants α).onThe
ory T ⊨ᵇ φ
参数：S : L[[α]].Theory。
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem setOfPred_subset_eq_univ_iff (S : L[[α]].Theory) :
    { p : T.CompleteType α | S ⊆ ↑p } = Set.univ ↔
      ∀ φ, φ ∈ S → (L.lhomWithConstants α).onTheory T ⊨ᵇ φ := by
  have h : { p : T.CompleteType α | S ⊆ ↑p } = ⋂₀ ((fun φ => { p | φ ∈ p }) '' S) := by
    ext
    simp [subset_def]
  simp_rw [h, sInter_eq_univ, ← setOfPred_mem_eq_univ_iff]
  refine ⟨fun h φ φS => h _ ⟨_, φS, rfl⟩, ?_⟩
  rintro h _ ⟨φ, h1, rfl⟩
  exact h _ h1

@[deprecated (since := "2026-07-09")] alias setOf_subset_eq_univ_iff := setOfPred_subset_eq_univ_iff
/-
**FirstOrder.Language.Theory.CompleteType.nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.Theory.CompleteType`。
形式化陈述：nonempty_iff : Nonempty (T.CompleteType α) ↔ T.IsSatisfiable
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Theory.isSatisfiable_onTheory_iff`：isSatisfiable_onT
heory_iff {L' : Language.{w, w'}} {φ : L ->ᴸ L'} (h : φ.Injective) : (φ.onTheory
 T).IsSatisfiable ↔ T.IsSatisfiable
· 使用定理 `FirstOrder.Language.lhomWithConstants_injective`：lhomWithConstants_injec
tive : (L.lhomWithConstants α).Injective
· 使用定理 `Set.nonempty_iff_univ_nonempty`：nonempty_iff_univ_nonempty : Nonempty α 
↔ (univ : Set α).Nonempty
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `FirstOrder.Language.Theory.CompleteType.setOfPred_subset_eq_empty_iff`：s
etOfPred_subset_eq_empty_iff (S : L[[α]].Theory) : { p : T.CompleteType α | S su
bseteq ↑p } = ∅ ↔ ¬((L.lhomWithConstants α).onTheory T unio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nonempty_iff : Nonempty (T.CompleteType α) ↔ T.IsSatisfiable := by
  rw [← isSatisfiable_onTheory_iff (lhomWithConstants_injective L α)]
  rw [nonempty_iff_univ_nonempty, nonempty_iff_ne_empty, Ne, not_iff_comm,
    ← union_empty ((L.lhomWithConstants α).onTheory T), ← setOfPred_subset_eq_empty_iff]
  simp
/-
**FirstOrder.Language.Theory.CompleteType.instNonempty** 是 Mathlib 中的一个实例，位于命名空间
 `FirstOrder.Language.Theory.CompleteType`。
形式化陈述：instNonempty : Nonempty (CompleteType (∅ : L.Theory) α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.Theory.CompleteType.nonempty_iff`：nonempty_iff : Non
empty (T.CompleteType α) ↔ T.IsSatisfiable
· 使用定理 `FirstOrder.Language.Theory.isSatisfiable_empty`：isSatisfiable_empty (L :
 Language.{u, v}) : IsSatisfiable (∅ : L.Theory)
-/
instance instNonempty : Nonempty (CompleteType (∅ : L.Theory) α) :=
  nonempty_iff.2 (isSatisfiable_empty L)
/-
**FirstOrder.Language.Theory.CompleteType.iInter_setOfPred_subset** 是 Mathlib 中的
一个定理，位于命名空间 `FirstOrder.Language.Theory.CompleteType`。
形式化陈述：iInter_setOfPred_subset {ι : Type*} (S : ι -> L[[α]].Theory) : ⋂ i : ι, { 
p : T.CompleteType α | S i subseteq p } = { p : T.CompleteType α | ⋃ i : ι, S i 
subseteq p }
参数：S : ι -> L[[α]].Theory。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iInter_setOfPred_subset {ι : Type*} (S : ι → L[[α]].Theory) :
    ⋂ i : ι, { p : T.CompleteType α | S i ⊆ p } =
      { p : T.CompleteType α | ⋃ i : ι, S i ⊆ p } := by
  ext
  simp only [mem_iInter, mem_ofPred_eq, iUnion_subset_iff]

@[deprecated (since := "2026-07-09")] alias iInter_setOf_subset := iInter_setOfPred_subset
/-
**FirstOrder.Language.Theory.CompleteType.toList_foldr_inf_mem** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language.Theory.CompleteType`。
形式化陈述：toList_foldr_inf_mem {p : T.CompleteType α} {t : Finset L[[α]].Sentence} :
 t.toList.foldr (· ⊓ ·) ⊤ in p ↔ (t : L[[α]].Theory) subseteq ↑p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FirstOrder.Language.Theory.IsMaximal.mem_iff_models`：∀ {L : FirstOrder.L
anguage} {T : L.Theory}, T.IsMaximal → ∀ (φ : L.Sentence), φ ∈ T ↔ T ⊨ᵇ φ
· 使用定理 `FirstOrder.Language.Theory.CompleteType.isMaximal`：isMaximal (p : T.Comp
leteType α) : IsMaximal (p : L[[α]].Theory)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem toList_foldr_inf_mem {p : T.CompleteType α} {t : Finset L[[α]].Sentence} :
    t.toList.foldr (· ⊓ ·) ⊤ ∈ p ↔ (t : L[[α]].Theory) ⊆ ↑p := by
  simp_rw [subset_def, ← SetLike.mem_coe, p.isMaximal.mem_iff_models, models_sentence_iff,
    Sentence.Realize, Formula.Realize, BoundedFormula.realize_foldr_inf, Finset.mem_toList]
  exact ⟨fun h φ hφ M => h _ _ hφ, fun h M φ hφ => h _ hφ _⟩

end CompleteType

variable {M : Type w'} [L.Structure M] [Nonempty M] [M ⊨ T] (T)

/-- The set of all formulas true at a tuple in a structure forms a complete type. -/
/-
**FirstOrder.Language.Theory.typeOf** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langua
ge.Theory`。
形式化陈述：typeOf (v : α -> M) : T.CompleteType α
参数：v : α -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of all formulas true at a tuple in a structure forms a complete type.
-/
def typeOf (v : α → M) : T.CompleteType α :=
  haveI : (constantsOn α).Structure M := constantsOn.structure v
  { toTheory := L[[α]].completeTheory M
    subset' := model_iff_subset_completeTheory.1 ((LHom.onTheory_model _ T).2 inferInstance)
    isMaximal' := completeTheory.isMaximal _ _ }

namespace CompleteType

variable {T} {v : α → M}

@[simp]
/-
**FirstOrder.Language.Theory.CompleteType.mem_typeOf** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.Theory.CompleteType`。
形式化陈述：mem_typeOf {φ : L[[α]].Sentence} : φ in T.typeOf v ↔ (Formula.equivSentenc
e.symm φ).Realize v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `FirstOrder.Language.mem_completeTheory`：mem_completeTheory {φ : Sentence
 L} : φ in L.completeTheory M ↔ M ⊨ φ
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `FirstOrder.Language.Formula.realize_equivSentence_symm`：realize_equivSen
tence_symm (φ : L[[α]].Sentence) (v : α -> M) : (equivSentence.symm φ).Realize v
 ↔ @Sentence.Realize _ M (@Language.withCons…
-/
theorem mem_typeOf {φ : L[[α]].Sentence} :
    φ ∈ T.typeOf v ↔ (Formula.equivSentence.symm φ).Realize v :=
  letI : (constantsOn α).Structure M := constantsOn.structure v
  mem_completeTheory.trans (Formula.realize_equivSentence_symm _ _ _).symm
/-
**FirstOrder.Language.Theory.CompleteType.formula_mem_typeOf** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language.Theory.CompleteType`。
形式化陈述：formula_mem_typeOf {φ : L.Formula α} : Formula.equivSentence φ in T.typeOf
 v ↔ φ.Realize v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem formula_mem_typeOf {φ : L.Formula α} :
    Formula.equivSentence φ ∈ T.typeOf v ↔ φ.Realize v := by simp

@[simp]
/-
**FirstOrder.Language.Theory.CompleteType.mem_typesWith_iff** 是 Mathlib 中的一个引理，位
于命名空间 `FirstOrder.Language.Theory.CompleteType`。
形式化陈述：mem_typesWith_iff (φ : L[[α]].Sentence) (p : CompleteType T α) : p in T.ty
pesWith φ ↔ φ in p
参数：φ : L[[α]].Sentence；p : CompleteType T α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_typesWith_iff (φ : L[[α]].Sentence) (p : CompleteType T α) :
    p ∈ T.typesWith φ ↔ φ ∈ p := by
  rfl
/-
**FirstOrder.Language.Theory.CompleteType.typesWith_inf** 是 Mathlib 中的一个引理，位于命名空
间 `FirstOrder.Language.Theory.CompleteType`。
形式化陈述：typesWith_inf (φ ψ : L[[α]].Sentence) : T.typesWith (φ ⊓ ψ) = T.typesWith 
φ inter T.typesWith ψ
参数：φ ψ : L[[α]].Sentence。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FirstOrder.Language.Theory.IsMaximal.mem_iff_models`：∀ {L : FirstOrder.L
anguage} {T : L.Theory}, T.IsMaximal → ∀ (φ : L.Sentence), φ ∈ T ↔ T ⊨ᵇ φ
· 使用定理 `FirstOrder.Language.Theory.CompleteType.isMaximal`：isMaximal (p : T.Comp
leteType α) : IsMaximal (p : L[[α]].Theory)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall₃_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {p q : (a : α) → (b : β a) → γ a b → Prop},   (∀ (a : α) (b : β a) (c 
: γ…
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_inf`：realize_inf : (φ ⊓ ψ).Re
alize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs
-/
lemma typesWith_inf (φ ψ : L[[α]].Sentence) :
    T.typesWith (φ ⊓ ψ) = T.typesWith φ ∩ T.typesWith ψ := by
  ext p
  simp only [mem_typesWith_iff, mem_inter_iff, ← SetLike.mem_coe, p.isMaximal.mem_iff_models,
    ModelsBoundedFormula, ← forall_and]
  exact forall₃_congr fun _ _ _ ↦ BoundedFormula.realize_inf
/-
**FirstOrder.Language.Theory.CompleteType.typesWith_eq_univ_of_mem_onTheory_lhom
WithConstants** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder.Language.Theory.CompleteType
`。
形式化陈述：typesWith_eq_univ_of_mem_onTheory_lhomWithConstants {φ} (hφ : φ in (L.lhom
WithConstants α).onTheory T) : T.typesWith φ = Set.univ
参数：hφ : φ in (L.lhomWithConstants α).onTheory T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `FirstOrder.Language.Theory.CompleteType.subset`：subset (p : T.CompleteTy
pe α) : (L.lhomWithConstants α).onTheory T subseteq (p : L[[α]].Theory)
-/
lemma typesWith_eq_univ_of_mem_onTheory_lhomWithConstants {φ}
    (hφ : φ ∈ (L.lhomWithConstants α).onTheory T) : T.typesWith φ = Set.univ :=
  univ_subset_iff.mp fun p _ ↦ p.subset hφ
/-
**FirstOrder.Language.Theory.CompleteType.typesWith_top** 是 Mathlib 中的一个引理，位于命名空
间 `FirstOrder.Language.Theory.CompleteType`。
形式化陈述：typesWith_top : T.typesWith (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `FirstOrder.Language.Theory.IsMaximal.mem_of_models`：∀ {L : FirstOrder.La
nguage} {T : L.Theory}, T.IsMaximal → ∀ {φ : L.Sentence}, T ⊨ᵇ φ → φ ∈ T
· 使用定理 `FirstOrder.Language.Theory.CompleteType.isMaximal`：isMaximal (p : T.Comp
leteType α) : IsMaximal (p : L[[α]].Theory)
-/
lemma typesWith_top : T.typesWith (α := α) ⊤ = Set.univ :=
  univ_subset_iff.mp fun p _ ↦ p.isMaximal.mem_of_models (φ := ⊤) (fun _ _ _ a ↦ a)
/-
**FirstOrder.Language.Theory.CompleteType.typesWith_not** 是 Mathlib 中的一个引理，位于命名空
间 `FirstOrder.Language.Theory.CompleteType`。
形式化陈述：typesWith_not (φ : L[[α]].Sentence) : T.typesWith ∼φ = (T.typesWith φ)ᶜ
参数：φ : L[[α]].Sentence。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Theory.CompleteType.compl_setOfPred_mem`：compl_setOf
Pred_mem {φ : L[[α]].Sentence} : { p : T.CompleteType α | φ in p }ᶜ = { p : T.Co
mpleteType α | φ.not in p }
-/
lemma typesWith_not (φ : L[[α]].Sentence) : T.typesWith ∼φ = (T.typesWith φ)ᶜ := by
  exact Eq.symm compl_setOfPred_mem

end CompleteType

variable (M)

/-- A complete type `p` is realized in a particular structure when there is some
  tuple `v` whose type is `p`. -/
@[simp]
/-
**FirstOrder.Language.Theory.realizedTypes** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder
.Language.Theory`。
形式化陈述：realizedTypes (α : Type w) : Set (T.CompleteType α)
参数：α : Type w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete type `p` is realized in a particular structure when there is some
  tuple `v` whose type is `p`.
-/
def realizedTypes (α : Type w) : Set (T.CompleteType α) :=
  Set.range (T.typeOf : (α → M) → T.CompleteType α)

section

set_option backward.isDefEq.respectTransparency false in
/-
**FirstOrder.Language.Theory.exists_modelType_is_realized_in** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language.Theory`。
形式化陈述：exists_modelType_is_realized_in (p : T.CompleteType α) : exists M : Theory
.ModelType.{u, v, max u v w} T, p in T.realizedTypes M α
参数：p : T.CompleteType α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `FirstOrder.Language.Theory.CompleteType.isMaximal`：isMaximal (p : T.Comp
leteType α) : IsMaximal (p : L[[α]].Theory)
· 使用定理 `FirstOrder.Language.Theory.CompleteType.subset`：subset (p : T.CompleteTy
pe α) : (L.lhomWithConstants α).onTheory T subseteq (p : L[[α]].Theory)
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `FirstOrder.Language.Formula.realize_equivSentence_symm_con`：realize_equi
vSentence_symm_con [L[[α]].Structure M] [(L.lhomWithConstants α).IsExpansionOn M
] (φ : L[[α]].Sentence) : ((equivSentence.symm φ…
· 使用定理 `FirstOrder.Language.LHom.isExpansionOn_reduct`：∀ {L : FirstOrder.Languag
e} {L' : FirstOrder.Language} (ϕ : L →ᴸ L') (M : Type u_1) [inst : L'.Structure 
M],   ϕ.IsExpansionOn M
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `FirstOrder.Language.Theory.IsComplete.realize_sentence_iff`：realize_sent
ence_iff (h : T.IsComplete) (φ : L.Sentence) (M : Type*) [L.Structure M] [M ⊨ T]
 [Nonempty M] : M ⊨ φ ↔ T ⊨ᵇ φ
· 使用定理 `FirstOrder.Language.Theory.IsMaximal.isComplete`：∀ {L : FirstOrder.Langu
age} {T : L.Theory}, T.IsMaximal → T.IsComplete
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `FirstOrder.Language.Theory.IsMaximal.mem_iff_models`：∀ {L : FirstOrder.L
anguage} {T : L.Theory}, T.IsMaximal → ∀ (φ : L.Sentence), φ ∈ T ↔ T ⊨ᵇ φ
-/
theorem exists_modelType_is_realized_in (p : T.CompleteType α) :
    ∃ M : Theory.ModelType.{u, v, max u v w} T, p ∈ T.realizedTypes M α := by
  obtain ⟨M⟩ := p.isMaximal.1
  refine ⟨(M.subtheoryModel p.subset).reduct (L.lhomWithConstants α), fun a => (L.con a : M), ?_⟩
  refine SetLike.ext fun φ => ?_
  simp only [CompleteType.mem_typeOf]
  refine
    (@Formula.realize_equivSentence_symm_con _
      ((M.subtheoryModel p.subset).reduct (L.lhomWithConstants α)) _ _ M.struc _ φ).trans
      (_root_.trans (_root_.trans ?_ (p.isMaximal.isComplete.realize_sentence_iff φ M))
        (p.isMaximal.mem_iff_models φ).symm)
  rfl

end

end Theory

end Language

end FirstOrder

