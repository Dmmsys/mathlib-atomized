/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.Ultraproducts
public import Mathlib.ModelTheory.Bundled
public import Mathlib.ModelTheory.Skolem
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# First-Order Satisfiability

This file deals with the satisfiability of first-order theories, as well as equivalence over them.

## Main Definitions

- `FirstOrder.Language.Theory.IsSatisfiable`: `T.IsSatisfiable` indicates that `T` has a nonempty
  model.
- `FirstOrder.Language.Theory.IsFinitelySatisfiable`: `T.IsFinitelySatisfiable` indicates that
  every finite subset of `T` is satisfiable.
- `FirstOrder.Language.Theory.IsComplete`: `T.IsComplete` indicates that `T` is satisfiable and
  models each sentence or its negation.
- `Cardinal.Categorical`: A theory is `κ`-categorical if all models of size `κ` are isomorphic.

## Main Results

- The Compactness Theorem, `FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable`,
  shows that a theory is satisfiable iff it is finitely satisfiable.
- `FirstOrder.Language.completeTheory.isComplete`: The complete theory of a structure is
  complete.
- `FirstOrder.Language.Theory.exists_large_model_of_infinite_model` shows that any theory with an
  infinite model has arbitrarily large models.
- `FirstOrder.Language.Theory.exists_elementaryEmbedding_card_eq`: The Upward Löwenheim–Skolem
  Theorem: If `κ` is a cardinal greater than the cardinalities of `L` and an infinite `L`-structure
  `M`, then `M` has an elementary extension of cardinality `κ`.

## Implementation Details

- Satisfiability of an `L.Theory` `T` is defined in the minimal universe containing all the symbols
  of `L`. By Löwenheim-Skolem, this is equivalent to satisfiability in any universe.
-/

@[expose] public section



universe u v w w'

open Cardinal CategoryTheory

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w} {n : ℕ}

namespace Theory

variable (T)

/-- A theory is satisfiable if a structure models it. -/
/-
**FirstOrder.Language.Theory.IsSatisfiable** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder
.Language.Theory`。
形式化陈述：IsSatisfiable : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A theory is satisfiable if a structure models it.
-/
def IsSatisfiable : Prop :=
  Nonempty (ModelType.{u, v, max u v} T)

/-- A theory is finitely satisfiable if all of its finite subtheories are satisfiable. -/
/-
**FirstOrder.Language.Theory.IsFinitelySatisfiable** 是 Mathlib 中的一个定义，位于命名空间 `Fi
rstOrder.Language.Theory`。
形式化陈述：IsFinitelySatisfiable : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A theory is finitely satisfiable if all of its finite subtheories are satisfiabl
e.
-/
def IsFinitelySatisfiable : Prop :=
  ∀ T0 : Finset L.Sentence, (T0 : L.Theory) ⊆ T → IsSatisfiable (T0 : L.Theory)

variable {T} {T' : L.Theory}
/-
**FirstOrder.Language.Theory.Model.isSatisfiable** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Theory.Model`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory} (M : Type w) [Nonempty M] [inst
 : L.Structure M] [M ⊨ T], T.IsSatisfiable
参数：M : Type w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `FirstOrder.Language.ElementarySubstructure.toModel.instSmall`：∀ {L : Fir
stOrder.Language} (T : L.Theory) {M : T.ModelType} (S : L.ElementarySubstructure
 ↑M) [h : Small.{w, x} ↥S],   Small.{w, x} ↑(First…
· 使用定理 `FirstOrder.Language.Substructure.elementarySkolem₁Reduct.instSmall`：∀ (L
 : FirstOrder.Language) (M : Type w) [inst : Nonempty M] [inst_1 : L.Structure M
],   Small.{max u v, w} ↥⊥.elementarySkolem₁Reduct
-/
theorem Model.isSatisfiable (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T] :
    T.IsSatisfiable :=
  ⟨((⊥ : Substructure _ (ModelType.of T M)).elementarySkolem₁Reduct.toModel T).shrink⟩
/-
**FirstOrder.Language.Theory.IsSatisfiable.mono** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Theory.IsSatisfiable`。
形式化陈述：∀ {L : FirstOrder.Language} {T T' : L.Theory}, T'.IsSatisfiable → T ⊆ T' →
 T.IsSatisfiable
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `FirstOrder.Language.Theory.Model.mono`：∀ {L : FirstOrder.Language} {M : 
Type w} [inst : L.Structure M] {T T' : L.Theory}, M ⊨ T' → T ⊆ T' → M ⊨ T
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
-/
theorem IsSatisfiable.mono (h : T'.IsSatisfiable) (hs : T ⊆ T') : T.IsSatisfiable :=
  ⟨(Theory.Model.mono (ModelType.is_model h.some) hs).bundled⟩
/-
**FirstOrder.Language.Theory.isSatisfiable_empty** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Theory`。
形式化陈述：isSatisfiable_empty (L : Language.{u, v}) : IsSatisfiable (∅ : L.Theory)
参数：L : Language.{u, v}。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isSatisfiable_empty (L : Language.{u, v}) : IsSatisfiable (∅ : L.Theory) :=
  ⟨default⟩
/-
**FirstOrder.Language.Theory.isSatisfiable_of_isSatisfiable_onTheory** 是 Mathlib
 中的一个定理，位于命名空间 `FirstOrder.Language.Theory`。
形式化陈述：isSatisfiable_of_isSatisfiable_onTheory {L' : Language.{w, w'}} (φ : L ->ᴸ
 L') (h : (φ.onTheory T).IsSatisfiable) : T.IsSatisfiable
参数：φ : L ->ᴸ L'；h : (φ.onTheory T).IsSatisfiable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.Model.isSatisfiable`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (M : Type w) [Nonempty M] [inst : L.Structure M] [M ⊨ T], T.I
sSatisfiable
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
-/
theorem isSatisfiable_of_isSatisfiable_onTheory {L' : Language.{w, w'}} (φ : L →ᴸ L')
    (h : (φ.onTheory T).IsSatisfiable) : T.IsSatisfiable :=
  Model.isSatisfiable (h.some.reduct φ)
/-
**FirstOrder.Language.Theory.isSatisfiable_onTheory_iff** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.Theory`。
形式化陈述：isSatisfiable_onTheory_iff {L' : Language.{w, w'}} {φ : L ->ᴸ L'} (h : φ.I
njective) : (φ.onTheory T).IsSatisfiable ↔ T.IsSatisfiable
参数：h : φ.Injective。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.isSatisfiable_of_isSatisfiable_onTheory`：isSa
tisfiable_of_isSatisfiable_onTheory {L' : Language.{w, w'}} (φ : L ->ᴸ L') (h : 
(φ.onTheory T).IsSatisfiable) : T.IsSatisfiable
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `FirstOrder.Language.Theory.Model.isSatisfiable`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (M : Type w) [Nonempty M] [inst : L.Structure M] [M ⊨ T], T.I
sSatisfiable
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
-/
theorem isSatisfiable_onTheory_iff {L' : Language.{w, w'}} {φ : L →ᴸ L'} (h : φ.Injective) :
    (φ.onTheory T).IsSatisfiable ↔ T.IsSatisfiable := by
  classical
    refine ⟨isSatisfiable_of_isSatisfiable_onTheory φ, fun h' => ?_⟩
    have : Inhabited h'.some := Classical.inhabited_of_nonempty'
    exact Model.isSatisfiable (h'.some.defaultExpansion h)
/-
**FirstOrder.Language.Theory.IsSatisfiable.isFinitelySatisfiable** 是 Mathlib 中的一
个定理，位于命名空间 `FirstOrder.Language.Theory.IsSatisfiable`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory}, T.IsSatisfiable → T.IsFinitely
Satisfiable
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.IsSatisfiable.mono`：∀ {L : FirstOrder.Languag
e} {T T' : L.Theory}, T'.IsSatisfiable → T ⊆ T' → T.IsSatisfiable
-/
theorem IsSatisfiable.isFinitelySatisfiable (h : T.IsSatisfiable) : T.IsFinitelySatisfiable :=
  fun _ => h.mono

/-- The **Compactness Theorem of first-order logic**: A theory is satisfiable if and only if it is
finitely satisfiable. -/
/-
**FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable** 是 Mathlib
 中的一个定理，位于命名空间 `FirstOrder.Language.Theory`。
形式化陈述：isSatisfiable_iff_isFinitelySatisfiable {T : L.Theory} : T.IsSatisfiable ↔
 T.IsFinitelySatisfiable
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.IsSatisfiable.isFinitelySatisfiable`：∀ {L : F
irstOrder.Language} {T : L.Theory}, T.IsSatisfiable → T.IsFinitelySatisfiable
· 使用定理 `Finset.map_subtype_subset`：map_subtype_subset {t : Set α} (s : Finset t)
 : ↑(s.map (Embedding.subtype _)) subseteq t
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Ultraproduct.sentence_realize`：sentence_realize (φ :
 L.Sentence) : (u : Filter α).Product M ⊨ φ ↔ forallᶠ a : α in u, M a ⊨ φ
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `Ultrafilter.of_le`：of_le (f : Filter α) [NeBot f] : ↑(of f) <= f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `FirstOrder.Language.Theory.realize_sentence_of_mem`：∀ {L : FirstOrder.La
nguage} {M : Type w} [inst : L.Structure M] (T : L.Theory) [M ⊨ T] {φ : L.Senten
ce}, φ ∈ T → M ⊨ φ
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `FirstOrder.Language.Ultraproduct.Product.instNonempty`：∀ {α : Type u_1} 
{M : α → Type u_2} {u : Ultrafilter α} [∀ (a : α), Nonempty (M a)], Nonempty ((↑
u).Product M)

--- 原说明 ---
The **Compactness Theorem of first-order logic**: A theory is satisfiable if and
 only if it is
finitely satisfiable.
-/
theorem isSatisfiable_iff_isFinitelySatisfiable {T : L.Theory} :
    T.IsSatisfiable ↔ T.IsFinitelySatisfiable :=
  ⟨Theory.IsSatisfiable.isFinitelySatisfiable, fun h => by
    set M : Finset T → Type max u v := fun T0 : Finset T =>
      (h (T0.map (Function.Embedding.subtype fun x => x ∈ T)) T0.map_subtype_subset).some.Carrier
    let M' := Filter.Product (Ultrafilter.of (Filter.atTop : Filter (Finset T))) M
    have h' : M' ⊨ T := by
      refine ⟨fun φ hφ => ?_⟩
      rw [Ultraproduct.sentence_realize]
      refine
        Filter.Eventually.filter_mono (Ultrafilter.of_le _)
          (Filter.eventually_atTop.2
            ⟨{⟨φ, hφ⟩}, fun s h' =>
              Theory.realize_sentence_of_mem (s.map (Function.Embedding.subtype fun x => x ∈ T))
                ?_⟩)
      simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe,
        Subtype.exists, exists_and_right, exists_eq_right]
      exact ⟨hφ, h' (Finset.mem_singleton_self _)⟩
    exact ⟨ModelType.of T M'⟩⟩
/-
**FirstOrder.Language.Theory.isSatisfiable_directed_union_iff** 是 Mathlib 中的一个定理
，位于命名空间 `FirstOrder.Language.Theory`。
形式化陈述：isSatisfiable_directed_union_iff {ι : Type*} [Nonempty ι] {T : ι -> L.Theo
ry} (h : Directed (· subseteq ·) T) : Theory.IsSatisfiable (⋃ i, T i) ↔ forall i
, (T i).IsSatisfiable
参数：h : Directed (· subseteq ·) T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.IsSatisfiable.mono`：∀ {L : FirstOrder.Languag
e} {T T' : L.Theory}, T'.IsSatisfiable → T ⊆ T' → T.IsSatisfiable
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable`：isSa
tisfiable_iff_isFinitelySatisfiable {T : L.Theory} : T.IsSatisfiable ↔ T.IsFinit
elySatisfiable
· 使用定理 `FirstOrder.Language.Theory.IsFinitelySatisfiable.eq_1`：∀ {L : FirstOrder
.Language} (T : L.Theory),   T.IsFinitelySatisfiable = ∀ (T0 : Finset L.Sentence
), ↑T0 ⊆ T → FirstOrder.Language.Theory.IsS…
· 使用引理 `Directed.exists_mem_subset_of_finset_subset_biUnion`：Directed.exists_mem
_subset_of_finset_subset_biUnion {α ι : Type*} [Nonempty ι] {f : ι -> Set α} (h 
: Directed (· subseteq ·) f) {s : Finset …
-/
theorem isSatisfiable_directed_union_iff {ι : Type*} [Nonempty ι] {T : ι → L.Theory}
    (h : Directed (· ⊆ ·) T) : Theory.IsSatisfiable (⋃ i, T i) ↔ ∀ i, (T i).IsSatisfiable := by
  refine ⟨fun h' i => h'.mono (Set.subset_iUnion _ _), fun h' => ?_⟩
  rw [isSatisfiable_iff_isFinitelySatisfiable, IsFinitelySatisfiable]
  intro T0 hT0
  obtain ⟨i, hi⟩ := h.exists_mem_subset_of_finset_subset_biUnion hT0
  exact (h' i).mono hi
/-
**FirstOrder.Language.Theory.isSatisfiable_union_distinctConstantsTheory_of_card
_le** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language.Theory`。
形式化陈述：isSatisfiable_union_distinctConstantsTheory_of_card_le (T : L.Theory) (s :
 Set α) (M : Type w') [Nonempty M] [L.Structure M] [M ⊨ T] (h : Cardinal.lift.{w
'} #s <= Cardinal.lift.{w} #M) : ((L.lhomWithConstants α).onTheory T union L.dis
tinctConstantsTheory s).IsSatisfiable
参数：T : L.Theory；s : Set α；M : Type w'；h : Cardinal.lift.{w'} #s <= Cardinal.lift
.{w} #M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)
· 使用定理 `FirstOrder.Language.Theory.Model.union`：∀ {L : FirstOrder.Language} {M :
 Type w} [inst : L.Structure M] {T T' : L.Theory}, M ⊨ T → M ⊨ T' → M ⊨ T ∪ T'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.LHom.onTheory_model`：∀ {L : FirstOrder.Language} {L'
 : FirstOrder.Language} {M : Type w} [inst : L.Structure M] [inst_1 : L'.Structu
re M]   (φ : L →ᴸ L') [φ.IsEx…
· 使用定理 `FirstOrder.Language.model_distinctConstantsTheory`：model_distinctConstan
tsTheory {M : Type w} [L[[α]].Structure M] (s : Set α) : M ⊨ L.distinctConstants
Theory s ↔ Set.InjOn (fun i : α => (L.c…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `FirstOrder.Language.Theory.Model.isSatisfiable`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (M : Type w) [Nonempty M] [inst : L.Structure M] [M ⊨ T], T.I
sSatisfiable
-/
theorem isSatisfiable_union_distinctConstantsTheory_of_card_le (T : L.Theory) (s : Set α)
    (M : Type w') [Nonempty M] [L.Structure M] [M ⊨ T]
    (h : Cardinal.lift.{w'} #s ≤ Cardinal.lift.{w} #M) :
    ((L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory s).IsSatisfiable := by
  have : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  rw [Cardinal.lift_mk_le'] at h
  let : (constantsOn α).Structure M := constantsOn.structure (Function.extend (↑) h.some default)
  have : M ⊨ (L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory s := by
    refine ((LHom.onTheory_model _ _).2 inferInstance).union ?_
    rw [model_distinctConstantsTheory]
    intro a as b bs ab
    rw [← Subtype.coe_mk a as, ← Subtype.coe_mk b bs, ← Subtype.ext_iff]
    exact
      h.some.injective
        ((Subtype.coe_injective.extend_apply h.some default ⟨a, as⟩).symm.trans
          (ab.trans (Subtype.coe_injective.extend_apply h.some default ⟨b, bs⟩)))
  exact Model.isSatisfiable M
/-
**FirstOrder.Language.Theory.isSatisfiable_union_distinctConstantsTheory_of_infi
nite** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language.Theory`。
形式化陈述：isSatisfiable_union_distinctConstantsTheory_of_infinite (T : L.Theory) (s 
: Set α) (M : Type w') [L.Structure M] [M ⊨ T] [Infinite M] : ((L.lhomWithConsta
nts α).onTheory T union L.distinctConstantsTheory s).IsSatisfiable
参数：T : L.Theory；s : Set α；M : Type w'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.distinctConstantsTheory_eq_iUnion`：distinctConstants
Theory_eq_iUnion (s : Set α) : L.distinctConstantsTheory s = ⋃ t : Finset s, L.d
istinctConstantsTheory (t.map (Function.Emb…
· 使用定理 `Set.union_iUnion`：union_iUnion [Nonempty ι] (s : Set β) (t : ι -> Set β)
 : (s union ⋃ i, t i) = ⋃ i, s union t i
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `FirstOrder.Language.Theory.isSatisfiable_directed_union_iff`：isSatisfiab
le_directed_union_iff {ι : Type*} [Nonempty ι] {T : ι -> L.Theory} (h : Directed
 (· subseteq ·) T) : Theory.IsSatisfiable (⋃ i, T…
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `Monotone.union`：Monotone.union [Preorder β] {f g : β -> Set α} (hf : Mon
otone f) (hg : Monotone g) : Monotone fun x => f x union g x
· 使用定理 `monotone_const`：monotone_const [Preorder α] [Preorder β] {c : β} : Monot
one fun _ : α => c
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `FirstOrder.Language.monotone_distinctConstantsTheory`：monotone_distinctC
onstantsTheory : Monotone (L.distinctConstantsTheory : Set α -> L[[α]].Theory)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用引理 `Set.monotone_image`：monotone_image : Monotone (image f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `FirstOrder.Language.Theory.isSatisfiable_union_distinctConstantsTheory_o
f_card_le`：isSatisfiable_union_distinctConstantsTheory_of_card_le (T : L.Theory)
 (s : Set α) (M : Type w') [Nonempty M] [L.Structure M] [M ⊨ T] (h : Ca…
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Infinite.instNontrivial`：∀ (α : Type u_4) [Infinite α], Nontrivial α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.lift_le_aleph0`：lift_le_aleph0 {c : Cardinal.{u}} : lift.{v} c 
<= ℵ₀ ↔ c <= ℵ₀
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.finset_card_lt_aleph0`：finset_card_lt_aleph0 (s : Finset α) : #
(↑s : Set α) < ℵ₀
· 使用定理 `Cardinal.aleph0_le_lift`：aleph0_le_lift {c : Cardinal.{u}} : ℵ₀ <= lift.
{v} c ↔ ℵ₀ <= c
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
-/
theorem isSatisfiable_union_distinctConstantsTheory_of_infinite (T : L.Theory) (s : Set α)
    (M : Type w') [L.Structure M] [M ⊨ T] [Infinite M] :
    ((L.lhomWithConstants α).onTheory T ∪ L.distinctConstantsTheory s).IsSatisfiable := by
  rw [distinctConstantsTheory_eq_iUnion, Set.union_iUnion, isSatisfiable_directed_union_iff]
  · exact fun t =>
      isSatisfiable_union_distinctConstantsTheory_of_card_le T _ M
        ((lift_le_aleph0.2 (finset_card_lt_aleph0 _).le).trans
          (aleph0_le_lift.2 (aleph0_le_mk M)))
  · apply Monotone.directed_le
    refine monotone_const.union (monotone_distinctConstantsTheory.comp ?_)
    simp only [Finset.coe_map, Function.Embedding.coe_subtype]
    exact Monotone.comp (g := Set.image ((↑) : s → α)) (f := ((↑) : Finset s → Set s))
      Set.monotone_image fun _ _ => Finset.coe_subset.2

/-- Any theory with an infinite model has arbitrarily large models. -/
/-
**FirstOrder.Language.Theory.exists_large_model_of_infinite_model** 是 Mathlib 中的
一个定理，位于命名空间 `FirstOrder.Language.Theory`。
形式化陈述：exists_large_model_of_infinite_model (T : L.Theory) (κ : Cardinal.{w}) (M 
: Type w') [L.Structure M] [M ⊨ T] [Infinite M] : exists N : ModelType.{_, _, ma
x u v w} T, Cardinal.lift.{max u v w} κ <= #N
参数：T : L.Theory；κ : Cardinal.{w}；M : Type w'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.isSatisfiable_union_distinctConstantsTheory_o
f_infinite`：isSatisfiable_union_distinctConstantsTheory_of_infinite (T : L.Theor
y) (s : Set α) (M : Type w') [L.Structure M] [M ⊨ T] [Infinite M] : ((L.…
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `FirstOrder.Language.Theory.Model.mono`：∀ {L : FirstOrder.Language} {M : 
Type w} [inst : L.Structure M] {T T' : L.Theory}, M ⊨ T' → T ⊆ T' → M ⊨ T
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Theory.ModelType.reduct_Carrier`：∀ {L : FirstOrder.L
anguage} {T : L.Theory} {L' : FirstOrder.Language} (φ : L →ᴸ L') (M : (φ.onTheor
y T).ModelType),   ↑(FirstOrder.Language.…
· 使用定理 `FirstOrder.Language.Theory.coe_of`：coe_of {M : Type w} [L.Structure M] [
Nonempty M] (h : M ⊨ T) : (h.bundled : Type w) = M
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_out`：mk_out (c : Cardinal) : #c.out = c
· 使用定理 `Cardinal.mk_univ`：mk_univ {α : Type u} : #(@univ α) = #α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `FirstOrder.Language.card_le_of_model_distinctConstantsTheory`：card_le_of
_model_distinctConstantsTheory (s : Set α) (M : Type w) [L[[α]].Structure M] [h 
: M ⊨ L.distinctConstantsTheory s] : Cardinal.lift…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Any theory with an infinite model has arbitrarily large models.
-/
theorem exists_large_model_of_infinite_model (T : L.Theory) (κ : Cardinal.{w}) (M : Type w')
    [L.Structure M] [M ⊨ T] [Infinite M] :
    ∃ N : ModelType.{_, _, max u v w} T, Cardinal.lift.{max u v w} κ ≤ #N := by
  obtain ⟨N⟩ :=
    isSatisfiable_union_distinctConstantsTheory_of_infinite T (Set.univ : Set κ.out) M
  refine ⟨(N.is_model.mono Set.subset_union_left).bundled.reduct _, ?_⟩
  have : N ⊨ distinctConstantsTheory _ _ := N.is_model.mono Set.subset_union_right
  rw [ModelType.reduct_Carrier, coe_of]
  refine _root_.trans (lift_le.2 (le_of_eq (Cardinal.mk_out κ).symm)) ?_
  rw [← mk_univ]
  refine
    (card_le_of_model_distinctConstantsTheory L Set.univ N).trans (lift_le.{max u v w}.1 ?_)
  rw [lift_lift]
/-
**FirstOrder.Language.Theory.isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finse
t** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language.Theory`。
形式化陈述：isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finset {ι : Type*} (T : ι ->
 L.Theory) : IsSatisfiable (⋃ i, T i) ↔ forall s : Finset ι, IsSatisfiable (⋃ i 
in s, T i)
参数：T : ι -> L.Theory。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.IsSatisfiable.mono`：∀ {L : FirstOrder.Languag
e} {T T' : L.Theory}, T'.IsSatisfiable → T ⊆ T' → T.IsSatisfiable
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.iUnion_subset_iff`：iUnion_subset_iff {s : ι -> Set α} {t : Set α} : 
⋃ i, s i subseteq t ↔ forall i, s i subseteq t
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable`：isSa
tisfiable_iff_isFinitelySatisfiable {T : L.Theory} : T.IsSatisfiable ↔ T.IsFinit
elySatisfiable
· 使用引理 `Directed.exists_mem_subset_of_finset_subset_biUnion`：Directed.exists_mem
_subset_of_finset_subset_biUnion {α ι : Type*} [Nonempty ι] {f : ι -> Set α} (h 
: Directed (· subseteq ·) f) {s : Finset …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `Set.iUnion_mono'`：iUnion_mono' {s : ι -> Set α} {t : ι₂ -> Set α} (h : f
orall i, exists j, s i subseteq t j) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `Set.iUnion_eq_iUnion_finset`：iUnion_eq_iUnion_finset (s : ι -> Set α) : 
⋃ i, s i = ⋃ t : Finset ι, ⋃ i in t, s i
-/
theorem isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finset {ι : Type*} (T : ι → L.Theory) :
    IsSatisfiable (⋃ i, T i) ↔ ∀ s : Finset ι, IsSatisfiable (⋃ i ∈ s, T i) := by
  refine
    ⟨fun h s => h.mono (Set.iUnion_mono fun _ => Set.iUnion_subset_iff.2 fun _ => refl _),
      fun h => ?_⟩
  rw [isSatisfiable_iff_isFinitelySatisfiable]
  intro s hs
  rw [Set.iUnion_eq_iUnion_finset] at hs
  obtain ⟨t, ht⟩ := Directed.exists_mem_subset_of_finset_subset_biUnion (by
    exact Monotone.directed_le fun t1 t2 (h : ∀ ⦃x⦄, x ∈ t1 → x ∈ t2) =>
      Set.iUnion_mono fun _ => Set.iUnion_mono' fun h1 => ⟨h h1, refl _⟩) hs
  exact (h t).mono ht

end Theory

variable (L)

/-- A version of The Downward Löwenheim–Skolem theorem where the structure `N` elementarily embeds
into `M`, but is not by type a substructure of `M`, and thus can be chosen to belong to the universe
of the cardinal `κ`.
-/
/-
**FirstOrder.Language.exists_elementaryEmbedding_card_eq_of_le** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language`。
形式化陈述：exists_elementaryEmbedding_card_eq_of_le (M : Type w') [L.Structure M] (κ 
: Cardinal.{w}) (h1 : ℵ₀ <= κ) (h2 : lift.{w} L.card <= Cardinal.lift.{max u v} 
κ) (h3 : lift.{w'} κ <= Cardinal.lift.{w} #M) : exists N : Bundled L.Structure, 
Nonempty (N ↪ₑ[L] M) ∧ #N = κ
参数：M : Type w'；κ : Cardinal.{w}；h1 : ℵ₀ <= κ；h2 : lift.{w} L.card <= Cardinal.li
ft.{max u v} κ；h3 : lift.{w'} κ <= Cardinal.lift.{w} #M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.exists_elementarySubstructure_card_eq`：exists_elemen
tarySubstructure_card_eq (s : Set M) (κ : Cardinal.{w'}) (h1 : ℵ₀ <= κ) (h2 : Ca
rdinal.lift.{w'} #s <= Cardinal.lift.{w} κ) (h3…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `Cardinal.lift_zero`：lift_zero : lift 0 = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.small_iff_lift_mk_lt_univ`：small_iff_lift_mk_lt_univ {α : Type 
u} : Small.{v} α ↔ Cardinal.lift.{v + 1, _} #α < univ.{v, max u (v + 1)}
· 使用定理 `lt_of_eq_of_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < 
c → a < c
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Cardinal.lift_lt_univ'`：lift_lt_univ' (c : Cardinal) : lift.{max (u + 1)
 v, u} c < univ.{u, v}
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Equiv.bundledInduced_α`：∀ (L : FirstOrder.Language) {M : Type w} [inst :
 L.Structure M] {N : Type w'} (g : M ≃ N),   ↑(Equiv.bundledInduced L g) = N
· 使用定理 `Cardinal.lift_mk_shrink'`：lift_mk_shrink' (α : Type u) [Small.{v} α] : C
ardinal.lift.{u} #(Shrink.{v} α) = Cardinal.lift.{v} #α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A version of The Downward Löwenheim–Skolem theorem where the structure `N` eleme
ntarily embeds
into `M`, but is not by type a substructure of `M`, and thus can be chosen to be
long to the universe
of the cardinal `κ`.
-/
theorem exists_elementaryEmbedding_card_eq_of_le (M : Type w') [L.Structure M]
    (κ : Cardinal.{w}) (h1 : ℵ₀ ≤ κ) (h2 : lift.{w} L.card ≤ Cardinal.lift.{max u v} κ)
    (h3 : lift.{w'} κ ≤ Cardinal.lift.{w} #M) :
    ∃ N : Bundled L.Structure, Nonempty (N ↪ₑ[L] M) ∧ #N = κ := by
  obtain ⟨S, _, hS⟩ := exists_elementarySubstructure_card_eq L ∅ κ h1 (by simp) h2 h3
  have : Small.{w} S := by
    rw [← lift_inj.{_, w + 1}, lift_lift, lift_lift] at hS
    exact small_iff_lift_mk_lt_univ.2 (lt_of_eq_of_lt hS κ.lift_lt_univ')
  refine
    ⟨(equivShrink S).bundledInduced L,
      ⟨S.subtype.comp (Equiv.bundledInducedEquiv L _).symm.toElementaryEmbedding⟩,
      lift_inj.1 (_root_.trans ?_ hS)⟩
  simp only [Equiv.bundledInduced_α, lift_mk_shrink']

section

/-- The **Upward Löwenheim–Skolem Theorem**: If `κ` is a cardinal greater than the cardinalities of
`L` and an infinite `L`-structure `M`, then `M` has an elementary extension of cardinality `κ`. -/
/-
**FirstOrder.Language.exists_elementaryEmbedding_card_eq_of_ge** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language`。
形式化陈述：exists_elementaryEmbedding_card_eq_of_ge (M : Type w') [L.Structure M] [iM
 : Infinite M] (κ : Cardinal.{w}) (h1 : Cardinal.lift.{w} L.card <= Cardinal.lif
t.{max u v} κ) (h2 : Cardinal.lift.{w} #M <= Cardinal.lift.{w'} κ) : exists N : 
Bundled L.Structure, Nonempty (M ↪ₑ[L] N) ∧ #N = κ
参数：M : Type w'；κ : Cardinal.{w}；h1 : Cardinal.lift.{w} L.card <= Cardinal.lift.{
max u v} κ；h2 : Cardinal.lift.{w} #M <= Cardinal.lift.{w'} κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.exists_large_model_of_infinite_model`：exists_
large_model_of_infinite_model (T : L.Theory) (κ : Cardinal.{w}) (M : Type w') [L
.Structure M] [M ⊨ T] [Infinite M] : exists N : Model…
· 使用定理 `FirstOrder.Language.exists_elementaryEmbedding_card_eq_of_le`：exists_ele
mentaryEmbedding_card_eq_of_le (M : Type w') [L.Structure M] (κ : Cardinal.{w}) 
(h1 : ℵ₀ <= κ) (h2 : lift.{w} L.card <= Cardinal.l…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.aleph0_le_lift`：aleph0_le_lift {c : Cardinal.{u}} : ℵ₀ <= lift.
{v} c ↔ ℵ₀ <= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FirstOrder.Language.card_withConstants`：card_withConstants : L[[α]].card
 = Cardinal.lift.{w'} L.card + Cardinal.lift.{max u v} #α
· 使用定理 `Cardinal.lift_add`：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = li
ft.{v} a + lift.{v} b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Cardinal.add_eq_max`：add_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) : a + b 
= max a b
· 使用定理 `Cardinal.infinite_iff`：infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ <= #α
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.theory_model_iff`：theory_model_i
ff (f : M ↪ₑ[L] N) (T : L.Theory) : M ⊨ T ↔ N ⊨ T
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
· 使用定理 `FirstOrder.Language.LHom.isExpansionOn_reduct`：∀ {L : FirstOrder.Languag
e} {L' : FirstOrder.Language} (ϕ : L →ᴸ L') (M : Type u_1) [inst : L'.Structure 
M],   ϕ.IsExpansionOn M

--- 原说明 ---
The **Upward Löwenheim–Skolem Theorem**: If `κ` is a cardinal greater than the c
ardinalities of
`L` and an infinite `L`-structure `M`, then `M` has an elementary extension of c
ardinality `κ`.
-/
theorem exists_elementaryEmbedding_card_eq_of_ge (M : Type w') [L.Structure M] [iM : Infinite M]
    (κ : Cardinal.{w}) (h1 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ)
    (h2 : Cardinal.lift.{w} #M ≤ Cardinal.lift.{w'} κ) :
    ∃ N : Bundled L.Structure, Nonempty (M ↪ₑ[L] N) ∧ #N = κ := by
  obtain ⟨N0, hN0⟩ := (L.elementaryDiagram M).exists_large_model_of_infinite_model κ M
  rw [← lift_le.{max u v}, lift_lift, lift_lift] at h2
  obtain ⟨N, ⟨NN0⟩, hN⟩ :=
    exists_elementaryEmbedding_card_eq_of_le L[[M]] N0 κ
      (aleph0_le_lift.1 ((aleph0_le_lift.2 (aleph0_le_mk M)).trans h2))
      (by
        simp only [card_withConstants, lift_add, lift_lift]
        rw [add_comm, add_eq_max (aleph0_le_lift.2 (infinite_iff.1 iM)), max_le_iff]
        rw [← lift_le.{w'}, lift_lift, lift_lift] at h1
        exact ⟨h2, h1⟩)
      (hN0.trans (by rw [← lift_umax, lift_id]))
  let := (lhomWithConstants L M).reduct N
  have h : N ⊨ L.elementaryDiagram M :=
    (NN0.theory_model_iff (L.elementaryDiagram M)).2 inferInstance
  refine ⟨Bundled.of N, ⟨?_⟩, hN⟩
  apply ElementaryEmbedding.ofModelsElementaryDiagram L M N

end

/-- The Löwenheim–Skolem Theorem: If `κ` is a cardinal greater than the cardinalities of `L`
and an infinite `L`-structure `M`, then there is an elementary embedding in the appropriate
direction between then `M` and a structure of cardinality `κ`. -/
/-
**FirstOrder.Language.exists_elementaryEmbedding_card_eq** 是 Mathlib 中的一个定理，位于命名
空间 `FirstOrder.Language`。
形式化陈述：exists_elementaryEmbedding_card_eq (M : Type w') [L.Structure M] [iM : Inf
inite M] (κ : Cardinal.{w}) (h1 : ℵ₀ <= κ) (h2 : lift.{w} L.card <= Cardinal.lif
t.{max u v} κ) : exists N : Bundled L.Structure, (Nonempty (N ↪ₑ[L] M) ∨ Nonempt
y (M ↪ₑ[L] N)) ∧ #N = κ
参数：M : Type w'；κ : Cardinal.{w}；h1 : ℵ₀ <= κ；h2 : lift.{w} L.card <= Cardinal.li
ft.{max u v} κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `FirstOrder.Language.exists_elementaryEmbedding_card_eq_of_le`：exists_ele
mentaryEmbedding_card_eq_of_le (M : Type w') [L.Structure M] (κ : Cardinal.{w}) 
(h1 : ℵ₀ <= κ) (h2 : lift.{w} L.card <= Cardinal.l…
· 使用定理 `FirstOrder.Language.exists_elementaryEmbedding_card_eq_of_ge`：exists_ele
mentaryEmbedding_card_eq_of_ge (M : Type w') [L.Structure M] [iM : Infinite M] (
κ : Cardinal.{w}) (h1 : Cardinal.lift.{w} L.card <…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
The Löwenheim–Skolem Theorem: If `κ` is a cardinal greater than the cardinalitie
s of `L`
and an infinite `L`-structure `M`, then there is an elementary embedding in the 
appropriate
direction between then `M` and a structure of cardinality `κ`.
-/
theorem exists_elementaryEmbedding_card_eq (M : Type w') [L.Structure M] [iM : Infinite M]
    (κ : Cardinal.{w}) (h1 : ℵ₀ ≤ κ) (h2 : lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : Bundled L.Structure, (Nonempty (N ↪ₑ[L] M) ∨ Nonempty (M ↪ₑ[L] N)) ∧ #N = κ := by
  cases le_or_gt (lift.{w'} κ) (Cardinal.lift.{w} #M) with
  | inl h =>
    obtain ⟨N, hN1, hN2⟩ := exists_elementaryEmbedding_card_eq_of_le L M κ h1 h2 h
    exact ⟨N, Or.inl hN1, hN2⟩
  | inr h =>
    obtain ⟨N, hN1, hN2⟩ := exists_elementaryEmbedding_card_eq_of_ge L M κ h2 (le_of_lt h)
    exact ⟨N, Or.inr hN1, hN2⟩

/-- A consequence of the Löwenheim–Skolem Theorem: If `κ` is a cardinal greater than the
cardinalities of `L` and an infinite `L`-structure `M`, then there is a structure of cardinality `κ`
elementarily equivalent to `M`. -/
/-
**FirstOrder.Language.exists_elementarilyEquivalent_card_eq** 是 Mathlib 中的一个定理，位
于命名空间 `FirstOrder.Language`。
形式化陈述：exists_elementarilyEquivalent_card_eq (M : Type w') [L.Structure M] [Infin
ite M] (κ : Cardinal.{w}) (h1 : ℵ₀ <= κ) (h2 : lift.{w} L.card <= Cardinal.lift.
{max u v} κ) : exists N : CategoryTheory.Bundled L.Structure, (M ≅[L] N) ∧ #N = 
κ
参数：M : Type w'；κ : Cardinal.{w}；h1 : ℵ₀ <= κ；h2 : lift.{w} L.card <= Cardinal.li
ft.{max u v} κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.exists_elementaryEmbedding_card_eq`：exists_elementar
yEmbedding_card_eq (M : Type w') [L.Structure M] [iM : Infinite M] (κ : Cardinal
.{w}) (h1 : ℵ₀ <= κ) (h2 : lift.{w} L.card <…
· 使用定理 `FirstOrder.Language.ElementarilyEquivalent.symm`：∀ {L : FirstOrder.Langu
age} {M : Type w} {N : Type u_1} [inst : L.Structure M] [inst_1 : L.Structure N]
,   L.ElementarilyEquivalent M N → L.…
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.elementarilyEquivalent`：elementa
rilyEquivalent (f : M ↪ₑ[L] N) : M ≅[L] N

--- 原说明 ---
A consequence of the Löwenheim–Skolem Theorem: If `κ` is a cardinal greater than
 the
cardinalities of `L` and an infinite `L`-structure `M`, then there is a structur
e of cardinality `κ`
elementarily equivalent to `M`.
-/
theorem exists_elementarilyEquivalent_card_eq (M : Type w') [L.Structure M] [Infinite M]
    (κ : Cardinal.{w}) (h1 : ℵ₀ ≤ κ) (h2 : lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : CategoryTheory.Bundled L.Structure, (M ≅[L] N) ∧ #N = κ := by
  obtain ⟨N, NM | MN, hNκ⟩ := exists_elementaryEmbedding_card_eq L M κ h1 h2
  · exact ⟨N, NM.some.elementarilyEquivalent.symm, hNκ⟩
  · exact ⟨N, MN.some.elementarilyEquivalent, hNκ⟩

variable {L}

namespace Theory

/-
**FirstOrder.Language.Theory.exists_model_card_eq** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Theory`。
形式化陈述：exists_model_card_eq (h : exists M : ModelType.{u, v, max u v} T, Infinite
 M) (κ : Cardinal.{w}) (h1 : ℵ₀ <= κ) (h2 : Cardinal.lift.{w} L.card <= Cardinal
.lift.{max u v} κ) : exists N : ModelType.{u, v, w} T, #N = κ
参数：h : exists M : ModelType.{u, v, max u v} T, Infinite M；κ : Cardinal.{w}；h1 : 
ℵ₀ <= κ；h2 : Cardinal.lift.{w} L.card <= Cardinal.lift.{max u v} κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.exists_elementarilyEquivalent_card_eq`：exists_elemen
tarilyEquivalent_card_eq (M : Type w') [L.Structure M] [Infinite M] (κ : Cardina
l.{w}) (h1 : ℵ₀ <= κ) (h2 : lift.{w} L.card <= …
· 使用定理 `FirstOrder.Language.ElementarilyEquivalent.nonempty`：nonempty [Mn : None
mpty M] (h : M ≅[L] N) : Nonempty N
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `FirstOrder.Language.ElementarilyEquivalent.theory_model`：theory_model [M
T : M ⊨ T] (h : M ≅[L] N) : N ⊨ T
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
-/
theorem exists_model_card_eq (h : ∃ M : ModelType.{u, v, max u v} T, Infinite M) (κ : Cardinal.{w})
    (h1 : ℵ₀ ≤ κ) (h2 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : ModelType.{u, v, w} T, #N = κ := by
  cases h with
  | intro M MI =>
    obtain ⟨N, hN, rfl⟩ := exists_elementarilyEquivalent_card_eq L M κ h1 h2
    have : Nonempty N := hN.nonempty
    exact ⟨hN.theory_model.bundled, rfl⟩

variable (T)

/-- A theory models a (bounded) formula when any of its nonempty models realizes that formula on all
  inputs. -/
/-
**FirstOrder.Language.Theory.ModelsBoundedFormula** 是 Mathlib 中的一个定义，位于命名空间 `Fir
stOrder.Language.Theory`。
形式化陈述：ModelsBoundedFormula (φ : L.BoundedFormula α n) : Prop
参数：φ : L.BoundedFormula α n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A theory models a (bounded) formula when any of its nonempty models realizes tha
t formula on all
  inputs.
-/
def ModelsBoundedFormula (φ : L.BoundedFormula α n) : Prop :=
  ∀ (M : ModelType.{u, v, max u v w} T) (v : α → M) (xs : Fin n → M), φ.Realize v xs

@[inherit_doc FirstOrder.Language.Theory.ModelsBoundedFormula]
infixl:51 " ⊨ᵇ " => ModelsBoundedFormula -- input using \|= or \vDash, but not using \models

variable {T}
/-
**FirstOrder.Language.Theory.models_formula_iff** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Theory`。
形式化陈述：models_formula_iff {φ : L.Formula α} : T ⊨ᵇ φ ↔ forall (M : ModelType.{u, 
v, max u v w} T) (v : α -> M), φ.Realize v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Unique.forall_iff`：forall_iff {p : α -> Prop} : (forall a, p a) ↔ p defa
ult
-/
theorem models_formula_iff {φ : L.Formula α} :
    T ⊨ᵇ φ ↔ ∀ (M : ModelType.{u, v, max u v w} T) (v : α → M), φ.Realize v :=
  forall_congr' fun _ => forall_congr' fun _ => Unique.forall_iff
/-
**FirstOrder.Language.Theory.models_sentence_iff** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Theory`。
形式化陈述：models_sentence_iff {φ : L.Sentence} : T ⊨ᵇ φ ↔ forall M : ModelType.{u, v
, max u v} T, M ⊨ φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `FirstOrder.Language.Theory.models_formula_iff`：models_formula_iff {φ : L
.Formula α} : T ⊨ᵇ φ ↔ forall (M : ModelType.{u, v, max u v w} T) (v : α -> M), 
φ.Realize v
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Unique.forall_iff`：forall_iff {p : α -> Prop} : (forall a, p a) ↔ p defa
ult
-/
theorem models_sentence_iff {φ : L.Sentence} : T ⊨ᵇ φ ↔ ∀ M : ModelType.{u, v, max u v} T, M ⊨ φ :=
  models_formula_iff.trans (forall_congr' fun _ => Unique.forall_iff)
/-
**FirstOrder.Language.Theory.models_sentence_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.Theory`。
形式化陈述：models_sentence_of_mem {φ : L.Sentence} (h : φ in T) : T ⊨ᵇ φ
参数：h : φ in T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.Theory.models_sentence_iff`：models_sentence_iff {φ :
 L.Sentence} : T ⊨ᵇ φ ↔ forall M : ModelType.{u, v, max u v} T, M ⊨ φ
· 使用定理 `FirstOrder.Language.Theory.realize_sentence_of_mem`：∀ {L : FirstOrder.La
nguage} {M : Type w} [inst : L.Structure M] (T : L.Theory) [M ⊨ T] {φ : L.Senten
ce}, φ ∈ T → M ⊨ φ
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
-/
theorem models_sentence_of_mem {φ : L.Sentence} (h : φ ∈ T) : T ⊨ᵇ φ :=
  models_sentence_iff.2 fun _ => realize_sentence_of_mem T h
/-
**FirstOrder.Language.Theory.models_iff_not_satisfiable** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.Theory`。
形式化陈述：models_iff_not_satisfiable (φ : L.Sentence) : T ⊨ᵇ φ ↔ ¬IsSatisfiable (T u
nion {φ.not})
参数：φ : L.Sentence。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Theory.models_sentence_iff`：models_sentence_iff {φ :
 L.Sentence} : T ⊨ᵇ φ ↔ forall M : ModelType.{u, v, max u v} T, M ⊨ φ
· 使用定理 `FirstOrder.Language.Theory.IsSatisfiable.eq_1`：∀ {L : FirstOrder.Languag
e} (T : L.Theory), T.IsSatisfiable = Nonempty T.ModelType
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `FirstOrder.Language.Sentence.realize_not`：realize_not : M ⊨ φ.not ↔ ¬M ⊨
 φ
· 使用定理 `FirstOrder.Language.Theory.realize_sentence_of_mem`：∀ {L : FirstOrder.La
nguage} {M : Type w} [inst : L.Structure M] (T : L.Theory) [M ⊨ T] {φ : L.Senten
ce}, φ ∈ T → M ⊨ φ
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
-/
theorem models_iff_not_satisfiable (φ : L.Sentence) : T ⊨ᵇ φ ↔ ¬IsSatisfiable (T ∪ {φ.not}) := by
  rw [models_sentence_iff, IsSatisfiable]
  refine
    ⟨fun h1 h2 =>
      (Sentence.realize_not _).1
        (realize_sentence_of_mem (T ∪ {Formula.not φ})
          (Set.subset_union_right (Set.mem_singleton _)))
        (h1 (h2.some.subtheoryModel Set.subset_union_left)),
      fun h M => ?_⟩
  contrapose h
  rw [← Sentence.realize_not] at h
  refine
    ⟨{  Carrier := M
        is_model := ⟨fun ψ hψ => hψ.elim (realize_sentence_of_mem _) fun h' => ?_⟩ }⟩
  rw [Set.mem_singleton_iff.1 h']
  exact h
/-
**FirstOrder.Language.Theory.ModelsBoundedFormula.realize_sentence** 是 Mathlib 中
的一个定理，位于命名空间 `FirstOrder.Language.Theory.ModelsBoundedFormula`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory} {φ : L.Sentence},   T ⊨ᵇ φ → ∀ 
(M : Type u_1) [inst : L.Structure M] [M ⊨ T] [Nonempty M], M ⊨ φ
参数：M : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Theory.model_iff`：∀ {L : FirstOrder.Language} {M : T
ype w} [inst : L.Structure M] (T : L.Theory), M ⊨ T ↔ ∀ φ ∈ T, M ⊨ φ
· 使用定理 `FirstOrder.Language.Theory.Model.isSatisfiable`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (M : Type w) [Nonempty M] [inst : L.Structure M] [M ⊨ T], T.I
sSatisfiable
· 使用定理 `FirstOrder.Language.Theory.models_iff_not_satisfiable`：models_iff_not_sa
tisfiable (φ : L.Sentence) : T ⊨ᵇ φ ↔ ¬IsSatisfiable (T union {φ.not})
-/
theorem ModelsBoundedFormula.realize_sentence {φ : L.Sentence} (h : T ⊨ᵇ φ) (M : Type*)
    [L.Structure M] [M ⊨ T] [Nonempty M] : M ⊨ φ := by
  rw [models_iff_not_satisfiable] at h
  contrapose h
  have : M ⊨ T ∪ {Formula.not φ} := by
    simp only [Set.union_singleton, model_iff, Set.mem_insert_iff, forall_eq_or_imp,
      Sentence.realize_not]
    rw [← model_iff]
    exact ⟨h, inferInstance⟩
  exact Model.isSatisfiable M
/-
**FirstOrder.Language.Theory.models_formula_iff_onTheory_models_equivSentence** 
是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language.Theory`。
形式化陈述：models_formula_iff_onTheory_models_equivSentence {φ : L.Formula α} : T ⊨ᵇ 
φ ↔ (L.lhomWithConstants α).onTheory T ⊨ᵇ Formula.equivSentence φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.Theory.models_sentence_iff`：models_sentence_iff {φ :
 L.Sentence} : T ⊨ᵇ φ ↔ forall M : ModelType.{u, v, max u v} T, M ⊨ φ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Formula.realize_equivSentence`：realize_equivSentence
 [L[[α]].Structure M] [(L.lhomWithConstants α).IsExpansionOn M] (φ : L.Formula α
) : (equivSentence φ).Realize M ↔ φ.Rea…
· 使用定理 `FirstOrder.Language.LHom.isExpansionOn_reduct`：∀ {L : FirstOrder.Languag
e} {L' : FirstOrder.Language} (ϕ : L →ᴸ L') (M : Type u_1) [inst : L'.Structure 
M],   ϕ.IsExpansionOn M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.LHom.onTheory_model`：∀ {L : FirstOrder.Language} {L'
 : FirstOrder.Language} {M : Type w} [inst : L.Structure M] [inst_1 : L'.Structu
re M]   (φ : L →ᴸ L') [φ.IsEx…
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `FirstOrder.Language.Theory.models_formula_iff`：models_formula_iff {φ : L
.Formula α} : T ⊨ᵇ φ ↔ forall (M : ModelType.{u, v, max u v w} T) (v : α -> M), 
φ.Realize v
· 使用定理 `FirstOrder.Language.Theory.ModelsBoundedFormula.realize_sentence`：∀ {L :
 FirstOrder.Language} {T : L.Theory} {φ : L.Sentence},   T ⊨ᵇ φ → ∀ (M : Type u_
1) [inst : L.Structure M] [M ⊨ T] [Nonempty M], M ⊨ φ
-/
theorem models_formula_iff_onTheory_models_equivSentence {φ : L.Formula α} :
    T ⊨ᵇ φ ↔ (L.lhomWithConstants α).onTheory T ⊨ᵇ Formula.equivSentence φ := by
  refine ⟨fun h => models_sentence_iff.2 (fun M => ?_),
    fun h => models_formula_iff.2 (fun M v => ?_)⟩
  · let := (L.lhomWithConstants α).reduct M
    rw [Formula.realize_equivSentence]
    have : M ⊨ T := (LHom.onTheory_model _ _).1 M.is_model -- why isn't M.is_model inferInstance?
    let M' := Theory.ModelType.of T M
    exact h M' (fun a => (L.con a : M)) _
  · let : (constantsOn α).Structure M := constantsOn.structure v
    have : M ⊨ (L.lhomWithConstants α).onTheory T := (LHom.onTheory_model _ _).2 inferInstance
    exact (Formula.realize_equivSentence _ _).1 (h.realize_sentence M)
/-
**FirstOrder.Language.Theory.ModelsBoundedFormula.realize_formula** 是 Mathlib 中的
一个定理，位于命名空间 `FirstOrder.Language.Theory.ModelsBoundedFormula`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory} {α : Type w} {φ : L.Formula α},
   T ⊨ᵇ φ → ∀ (M : Type u_1) [inst : L.Structure M] [M ⊨ T] [Nonempty M] {v : α 
→ M}, φ.Realize v
参数：M : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.LHom.onTheory_model`：∀ {L : FirstOrder.Language} {L'
 : FirstOrder.Language} {M : Type w} [inst : L.Structure M] [inst_1 : L'.Structu
re M]   (φ : L →ᴸ L') [φ.IsEx…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Formula.realize_equivSentence`：realize_equivSentence
 [L[[α]].Structure M] [(L.lhomWithConstants α).IsExpansionOn M] (φ : L.Formula α
) : (equivSentence φ).Realize M ↔ φ.Rea…
· 使用定理 `FirstOrder.Language.Theory.ModelsBoundedFormula.realize_sentence`：∀ {L :
 FirstOrder.Language} {T : L.Theory} {φ : L.Sentence},   T ⊨ᵇ φ → ∀ (M : Type u_
1) [inst : L.Structure M] [M ⊨ T] [Nonempty M], M ⊨ φ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Theory.models_formula_iff_onTheory_models_equivSente
nce`：models_formula_iff_onTheory_models_equivSentence {φ : L.Formula α} : T ⊨ᵇ φ
 ↔ (L.lhomWithConstants α).onTheory T ⊨ᵇ Formula.equivSentence φ
-/
theorem ModelsBoundedFormula.realize_formula {φ : L.Formula α} (h : T ⊨ᵇ φ) (M : Type*)
    [L.Structure M] [M ⊨ T] [Nonempty M] {v : α → M} : φ.Realize v := by
  rw [models_formula_iff_onTheory_models_equivSentence] at h
  let : (constantsOn α).Structure M := constantsOn.structure v
  have : M ⊨ (L.lhomWithConstants α).onTheory T := (LHom.onTheory_model _ _).2 inferInstance
  exact (Formula.realize_equivSentence _ _).1 (h.realize_sentence M)
/-
**FirstOrder.Language.Theory.models_toFormula_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Theory`。
形式化陈述：models_toFormula_iff {φ : L.BoundedFormula α n} : T ⊨ᵇ φ.toFormula ↔ T ⊨ᵇ 
φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.ModelsBoundedFormula.realize_formula`：∀ {L : 
FirstOrder.Language} {T : L.Theory} {α : Type w} {φ : L.Formula α},   T ⊨ᵇ φ → ∀
 (M : Type u_1) [inst : L.Structure M] [M ⊨ T] [Nonem…
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem models_toFormula_iff {φ : L.BoundedFormula α n} : T ⊨ᵇ φ.toFormula ↔ T ⊨ᵇ φ := by
  refine ⟨fun h M v xs => ?_, ?_⟩
  · have h' : φ.toFormula.Realize (Sum.elim v xs) := h.realize_formula M
    simp only [BoundedFormula.realize_toFormula, Sum.elim_comp_inl, Sum.elim_comp_inr] at h'
    exact h'
  · simp only [models_formula_iff, BoundedFormula.realize_toFormula]
    exact fun h M v => h M _ _
/-
**FirstOrder.Language.Theory.ModelsBoundedFormula.realize_boundedFormula** 是 Mat
hlib 中的一个定理，位于命名空间 `FirstOrder.Language.Theory.ModelsBoundedFormula`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory} {α : Type w} {n : ℕ} {φ : L.Bou
ndedFormula α n},   T ⊨ᵇ φ → ∀ (M : Type u_1) [inst : L.Structure M] [M ⊨ T] [No
nempty M] {v : α → M} {xs : Fin n → M}, φ.Realize v xs
参数：M : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.ModelsBoundedFormula.realize_formula`：∀ {L : 
FirstOrder.Language} {T : L.Theory} {α : Type w} {φ : L.Formula α},   T ⊨ᵇ φ → ∀
 (M : Type u_1) [inst : L.Structure M] [M ⊨ T] [Nonem…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.Theory.models_toFormula_iff`：models_toFormula_iff {φ
 : L.BoundedFormula α n} : T ⊨ᵇ φ.toFormula ↔ T ⊨ᵇ φ
-/
theorem ModelsBoundedFormula.realize_boundedFormula
    {φ : L.BoundedFormula α n} (h : T ⊨ᵇ φ) (M : Type*)
    [L.Structure M] [M ⊨ T] [Nonempty M] {v : α → M} {xs : Fin n → M} : φ.Realize v xs := by
  have h' : φ.toFormula.Realize (Sum.elim v xs) := (models_toFormula_iff.2 h).realize_formula M
  simp only [BoundedFormula.realize_toFormula, Sum.elim_comp_inl, Sum.elim_comp_inr] at h'
  exact h'
/-
**FirstOrder.Language.Theory.models_of_models_theory** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.Theory`。
形式化陈述：models_of_models_theory {T' : L.Theory} (h : forall φ : L.Sentence, φ in T
' -> T ⊨ᵇ φ) {φ : L.Formula α} (hφ : T' ⊨ᵇ φ) : T ⊨ᵇ φ
参数：h : forall φ : L.Sentence, φ in T' -> T ⊨ᵇ φ；hφ : T' ⊨ᵇ φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.Theory.model_iff`：∀ {L : FirstOrder.Language} {M : T
ype w} [inst : L.Structure M] (T : L.Theory), M ⊨ T ↔ ∀ φ ∈ T, M ⊨ φ
· 使用定理 `FirstOrder.Language.Theory.ModelsBoundedFormula.realize_sentence`：∀ {L :
 FirstOrder.Language} {T : L.Theory} {φ : L.Sentence},   T ⊨ᵇ φ → ∀ (M : Type u_
1) [inst : L.Structure M] [M ⊨ T] [Nonempty M], M ⊨ φ
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
-/
theorem models_of_models_theory {T' : L.Theory}
    (h : ∀ φ : L.Sentence, φ ∈ T' → T ⊨ᵇ φ)
    {φ : L.Formula α} (hφ : T' ⊨ᵇ φ) : T ⊨ᵇ φ := fun M => by
  have hM : M ⊨ T' := T'.model_iff.2 (fun ψ hψ => (h ψ hψ).realize_sentence M)
  let M' : ModelType T' := ⟨M⟩
  exact hφ M'

/-- An alternative statement of the Compactness Theorem. A formula `φ` is modeled by a
theory iff there is a finite subset `T0` of the theory such that `φ` is modeled by `T0` -/
/-
**FirstOrder.Language.Theory.models_iff_finset_models** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.Theory`。
形式化陈述：models_iff_finset_models {φ : L.Sentence} : T ⊨ᵇ φ ↔ exists T0 : Finset L.
Sentence, (T0 : L.Theory) subseteq T ∧ (T0 : L.Theory) ⊨ᵇ φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable`：isSa
tisfiable_iff_isFinitelySatisfiable {T : L.Theory} : T.IsSatisfiable ↔ T.IsFinit
elySatisfiable
· 使用定理 `FirstOrder.Language.Theory.IsFinitelySatisfiable.eq_1`：∀ {L : FirstOrder
.Language} (T : L.Theory),   T.IsFinitelySatisfiable = ∀ (T0 : Finset L.Sentence
), ↑T0 ⊆ T → FirstOrder.Language.Theory.IsS…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₂`：contrapose_iff₂ {p q : Prop} 
: (p ↔ ¬ q) -> (¬ p ↔ q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用引理 `Finset.union_singleton`：union_singleton (x : α) (s : Finset α) : s union
 {x} = insert x s
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `FirstOrder.Language.Theory.IsSatisfiable.mono`：∀ {L : FirstOrder.Languag
e} {T T' : L.Theory}, T'.IsSatisfiable → T ⊆ T' → T.IsSatisfiable
· 使用定理 `Finset.coe_erase`：coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \
 {a} : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s

--- 原说明 ---
An alternative statement of the Compactness Theorem. A formula `φ` is modeled by
 a
theory iff there is a finite subset `T0` of the theory such that `φ` is modeled 
by `T0`
-/
theorem models_iff_finset_models {φ : L.Sentence} :
    T ⊨ᵇ φ ↔ ∃ T0 : Finset L.Sentence, (T0 : L.Theory) ⊆ T ∧ (T0 : L.Theory) ⊨ᵇ φ := by
  simp only [models_iff_not_satisfiable]
  rw [isSatisfiable_iff_isFinitelySatisfiable, IsFinitelySatisfiable]
  contrapose!
  let := Classical.decEq (Sentence L)
  constructor
  · intro h T0 hT0
    simpa using h (T0 ∪ {Formula.not φ})
      (by
        simp only [Finset.coe_union, Finset.coe_singleton]
        exact Set.union_subset_union hT0 (Set.Subset.refl _))
  · intro h T0 hT0
    exact IsSatisfiable.mono (h (T0.erase (Formula.not φ))
      (by simpa using hT0)) (by simp)

/-- A theory is complete when it is satisfiable and models each sentence or its negation. -/
/-
**FirstOrder.Language.Theory.IsComplete** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.La
nguage.Theory`。
形式化陈述：IsComplete (T : L.Theory) : Prop
参数：T : L.Theory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A theory is complete when it is satisfiable and models each sentence or its nega
tion.
-/
def IsComplete (T : L.Theory) : Prop :=
  T.IsSatisfiable ∧ ∀ φ : L.Sentence, T ⊨ᵇ φ ∨ T ⊨ᵇ φ.not

namespace IsComplete

/-
**FirstOrder.Language.Theory.IsComplete.models_not_iff** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.Theory.IsComplete`。
形式化陈述：models_not_iff (h : T.IsComplete) (φ : L.Sentence) : T ⊨ᵇ φ.not ↔ ¬T ⊨ᵇ φ
参数：h : T.IsComplete；φ : L.Sentence。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `FirstOrder.Language.Theory.models_sentence_iff`：models_sentence_iff {φ :
 L.Sentence} : T ⊨ᵇ φ ↔ forall M : ModelType.{u, v, max u v} T, M ⊨ φ
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
-/
theorem models_not_iff (h : T.IsComplete) (φ : L.Sentence) : T ⊨ᵇ φ.not ↔ ¬T ⊨ᵇ φ := by
  rcases h.2 φ with hφ | hφn
  · simp only [hφ, not_true, iff_false]
    rw [models_sentence_iff, not_forall]
    refine ⟨h.1.some, ?_⟩
    simp only [Sentence.realize_not, Classical.not_not]
    exact models_sentence_iff.1 hφ _
  · simp only [hφn, true_iff]
    intro hφ
    rw [models_sentence_iff] at *
    exact hφn h.1.some (hφ _)
/-
**FirstOrder.Language.Theory.IsComplete.realize_sentence_iff** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language.Theory.IsComplete`。
形式化陈述：realize_sentence_iff (h : T.IsComplete) (φ : L.Sentence) (M : Type*) [L.St
ructure M] [M ⊨ T] [Nonempty M] : M ⊨ φ ↔ T ⊨ᵇ φ
参数：h : T.IsComplete；φ : L.Sentence；M : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `FirstOrder.Language.Theory.ModelsBoundedFormula.realize_sentence`：∀ {L :
 FirstOrder.Language} {T : L.Theory} {φ : L.Sentence},   T ⊨ᵇ φ → ∀ (M : Type u_
1) [inst : L.Structure M] [M ⊨ T] [Nonempty M], M ⊨ φ
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Sentence.realize_not`：realize_not : M ⊨ φ.not ↔ ¬M ⊨
 φ
· 使用定理 `FirstOrder.Language.Theory.IsComplete.models_not_iff`：models_not_iff (h 
: T.IsComplete) (φ : L.Sentence) : T ⊨ᵇ φ.not ↔ ¬T ⊨ᵇ φ
-/
theorem realize_sentence_iff (h : T.IsComplete) (φ : L.Sentence) (M : Type*) [L.Structure M]
    [M ⊨ T] [Nonempty M] : M ⊨ φ ↔ T ⊨ᵇ φ := by
  rcases h.2 φ with hφ | hφn
  · exact iff_of_true (hφ.realize_sentence M) hφ
  · exact
      iff_of_false ((Sentence.realize_not M).1 (hφn.realize_sentence M))
        ((h.models_not_iff φ).1 hφn)

/-- A complete theory is the `completeTheory` Th(M) of one of its models. -/
/-
**FirstOrder.Language.Theory.IsComplete.eq_complete_theory** 是 Mathlib 中的一个定理，位于
命名空间 `FirstOrder.Language.Theory.IsComplete`。
形式化陈述：eq_complete_theory (h : T.IsComplete) (M : Type*) [L.Structure M] [M ⊨ T] 
[Nonempty M] : {φ | T ⊨ᵇ φ} = L.completeTheory M
参数：h : T.IsComplete；M : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.mem_completeTheory`：mem_completeTheory {φ : Sentence
 L} : φ in L.completeTheory M ↔ M ⊨ φ
· 使用定理 `FirstOrder.Language.Theory.ModelsBoundedFormula.realize_sentence`：∀ {L :
 FirstOrder.Language} {T : L.Theory} {φ : L.Sentence},   T ⊨ᵇ φ → ∀ (M : Type u_
1) [inst : L.Structure M] [M ⊨ T] [Nonempty M], M ⊨ φ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `FirstOrder.Language.Sentence.realize_not`：realize_not : M ⊨ φ.not ↔ ¬M ⊨
 φ

--- 原说明 ---
A complete theory is the `completeTheory` Th(M) of one of its models.
-/
theorem eq_complete_theory (h : T.IsComplete) (M : Type*) [L.Structure M] [M ⊨ T] [Nonempty M] :
    {φ | T ⊨ᵇ φ} = L.completeTheory M := by
  ext φ
  simp only [Set.mem_ofPred_eq, L.mem_completeTheory]
  refine ⟨fun h_models => h_models.realize_sentence M, fun h_realize => ?_⟩
  cases h.2 φ with
  | inl hT => exact hT
  | inr hT =>
      have : M ⊨ φ.not := hT.realize_sentence M
      rw [Sentence.realize_not] at this
      contradiction

/-- A theory is complete iff it is satisfiable and all its models are elementarily equivalent. -/
/-
**FirstOrder.Language.Theory.IsComplete.isComplete_iff_models_elementarily_equiv
alent** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language.Theory.IsComplete`。
形式化陈述：isComplete_iff_models_elementarily_equivalent : T.IsComplete ↔ T.IsSatisfi
able ∧ forall (M N : ModelType.{u, v, max u v} T), ElementarilyEquivalent L M N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.ElementarilyEquivalent.eq_1`：∀ (L : FirstOrder.Langu
age) (M : Type w) (N : Type u_1) [inst : L.Structure M] [inst_1 : L.Structure N]
,   L.ElementarilyEquivalent M N = (L…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Theory.IsComplete.eq_complete_theory`：eq_complete_th
eory (h : T.IsComplete) (M : Type*) [L.Structure M] [M ⊨ T] [Nonempty M] : {φ | 
T ⊨ᵇ φ} = L.completeTheory M
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.Theory.models_sentence_iff`：models_sentence_iff {φ :
 L.Sentence} : T ⊨ᵇ φ ↔ forall M : ModelType.{u, v, max u v} T, M ⊨ φ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.elementarilyEquivalent_iff`：elementarilyEquivalent_i
ff : M ≅[L] N ↔ forall φ : L.Sentence, M ⊨ φ ↔ N ⊨ φ
· 使用定理 `FirstOrder.Language.Sentence.realize_not`：realize_not : M ⊨ φ.not ↔ ¬M ⊨
 φ
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a

--- 原说明 ---
A theory is complete iff it is satisfiable and all its models are elementarily e
quivalent.
-/
theorem isComplete_iff_models_elementarily_equivalent :
    T.IsComplete ↔
    T.IsSatisfiable ∧ ∀ (M N : ModelType.{u, v, max u v} T), ElementarilyEquivalent L M N := by
  constructor
  · intro hcomp
    refine ⟨hcomp.1, ?_⟩
    intro M N
    rw [ElementarilyEquivalent, ← hcomp.eq_complete_theory, ← hcomp.eq_complete_theory]
  · rintro ⟨hsat, h⟩
    refine ⟨hsat, ?_⟩
    intro φ
    obtain ⟨M⟩ := hsat
    by_cases hφ : M ⊨ φ
    · left
      exact models_sentence_iff.2 fun N => (elementarilyEquivalent_iff.1 (h M N) φ).1 hφ
    · right
      exact models_sentence_iff.2 fun N => (Sentence.realize_not N).2
        (mt (elementarilyEquivalent_iff.1 (h M N) φ).2 hφ)

/-- If a theory is complete all its models are elementarily equivalent. -/
/-
**FirstOrder.Language.Theory.IsComplete.models_elementarily_equivalent** 是 Mathl
ib 中的一个定理，位于命名空间 `FirstOrder.Language.Theory.IsComplete`。
形式化陈述：models_elementarily_equivalent (h : T.IsComplete) (M N : Type*) [L.Structu
re M] [L.Structure N] [M ⊨ T] [N ⊨ T] [Nonempty M] [Nonempty N] : ElementarilyEq
uivalent L M N
参数：h : T.IsComplete；M N : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.ElementarilyEquivalent.eq_1`：∀ (L : FirstOrder.Langu
age) (M : Type w) (N : Type u_1) [inst : L.Structure M] [inst_1 : L.Structure N]
,   L.ElementarilyEquivalent M N = (L…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Theory.IsComplete.eq_complete_theory`：eq_complete_th
eory (h : T.IsComplete) (M : Type*) [L.Structure M] [M ⊨ T] [Nonempty M] : {φ | 
T ⊨ᵇ φ} = L.completeTheory M

--- 原说明 ---
If a theory is complete all its models are elementarily equivalent.
-/
theorem models_elementarily_equivalent
    (h : T.IsComplete)
    (M N : Type*) [L.Structure M] [L.Structure N]
    [M ⊨ T] [N ⊨ T] [Nonempty M] [Nonempty N] :
    ElementarilyEquivalent L M N := by
  rw [ElementarilyEquivalent, ← h.eq_complete_theory, ← h.eq_complete_theory]

end IsComplete

/-- A theory is maximal when it is satisfiable and contains each sentence or its negation.
  Maximal theories are complete. -/
/-
**FirstOrder.Language.Theory.IsMaximal** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lan
guage.Theory`。
形式化陈述：IsMaximal (T : L.Theory) : Prop
参数：T : L.Theory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A theory is maximal when it is satisfiable and contains each sentence or its neg
ation.
  Maximal theories are complete.
-/
def IsMaximal (T : L.Theory) : Prop :=
  T.IsSatisfiable ∧ ∀ φ : L.Sentence, φ ∈ T ∨ φ.not ∈ T
/-
**FirstOrder.Language.Theory.IsMaximal.isComplete** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Theory.IsMaximal`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory}, T.IsMaximal → T.IsComplete
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `FirstOrder.Language.Theory.models_sentence_of_mem`：models_sentence_of_me
m {φ : L.Sentence} (h : φ in T) : T ⊨ᵇ φ
-/
theorem IsMaximal.isComplete (h : T.IsMaximal) : T.IsComplete :=
  h.imp_right (forall_imp fun _ => Or.imp models_sentence_of_mem models_sentence_of_mem)
/-
**FirstOrder.Language.Theory.IsMaximal.mem_or_not_mem** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.Theory.IsMaximal`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory},   T.IsMaximal → ∀ (φ : L.Sente
nce), φ ∈ T ∨ FirstOrder.Language.Formula.not φ ∈ T
参数：φ : L.Sentence。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsMaximal.mem_or_not_mem (h : T.IsMaximal) (φ : L.Sentence) : φ ∈ T ∨ φ.not ∈ T :=
  h.2 φ
/-
**FirstOrder.Language.Theory.IsMaximal.mem_of_models** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.Theory.IsMaximal`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory}, T.IsMaximal → ∀ {φ : L.Sentenc
e}, T ⊨ᵇ φ → φ ∈ T
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `FirstOrder.Language.Theory.IsMaximal.mem_or_not_mem`：∀ {L : FirstOrder.L
anguage} {T : L.Theory},   T.IsMaximal → ∀ (φ : L.Sentence), φ ∈ T ∨ FirstOrder.
Language.Formula.not φ ∈ T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `FirstOrder.Language.Theory.models_iff_not_satisfiable`：models_iff_not_sa
tisfiable (φ : L.Sentence) : T ⊨ᵇ φ ↔ ¬IsSatisfiable (T union {φ.not})
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsMaximal.mem_of_models (h : T.IsMaximal) {φ : L.Sentence} (hφ : T ⊨ᵇ φ) : φ ∈ T := by
  refine (h.mem_or_not_mem φ).resolve_right fun con => ?_
  rw [models_iff_not_satisfiable, Set.union_singleton, Set.insert_eq_of_mem con] at hφ
  exact hφ h.1
/-
**FirstOrder.Language.Theory.IsMaximal.mem_iff_models** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.Theory.IsMaximal`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory}, T.IsMaximal → ∀ (φ : L.Sentenc
e), φ ∈ T ↔ T ⊨ᵇ φ
参数：φ : L.Sentence。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.models_sentence_of_mem`：models_sentence_of_me
m {φ : L.Sentence} (h : φ in T) : T ⊨ᵇ φ
· 使用定理 `FirstOrder.Language.Theory.IsMaximal.mem_of_models`：∀ {L : FirstOrder.La
nguage} {T : L.Theory}, T.IsMaximal → ∀ {φ : L.Sentence}, T ⊨ᵇ φ → φ ∈ T
-/
theorem IsMaximal.mem_iff_models (h : T.IsMaximal) (φ : L.Sentence) : φ ∈ T ↔ T ⊨ᵇ φ :=
  ⟨models_sentence_of_mem, h.mem_of_models⟩

end Theory

namespace completeTheory

variable (L) (M : Type w)
variable [L.Structure M]

/-
**FirstOrder.Language.completeTheory.isSatisfiable** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.completeTheory`。
形式化陈述：isSatisfiable [Nonempty M] : (L.completeTheory M).IsSatisfiable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.Model.isSatisfiable`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (M : Type w) [Nonempty M] [inst : L.Structure M] [M ⊨ T], T.I
sSatisfiable
-/
theorem isSatisfiable [Nonempty M] : (L.completeTheory M).IsSatisfiable :=
  Theory.Model.isSatisfiable M
/-
**FirstOrder.Language.completeTheory.mem_or_not_mem** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.completeTheory`。
形式化陈述：mem_or_not_mem (φ : L.Sentence) : φ in L.completeTheory M ∨ φ.not in L.com
pleteTheory M
参数：φ : L.Sentence。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem mem_or_not_mem (φ : L.Sentence) : φ ∈ L.completeTheory M ∨ φ.not ∈ L.completeTheory M := by
  simp_rw [completeTheory, Set.mem_ofPred_eq, Sentence.Realize, Formula.realize_not, or_not]
/-
**FirstOrder.Language.completeTheory.isMaximal** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.completeTheory`。
形式化陈述：isMaximal [Nonempty M] : (L.completeTheory M).IsMaximal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.completeTheory.isSatisfiable`：isSatisfiable [Nonempt
y M] : (L.completeTheory M).IsSatisfiable
· 使用定理 `FirstOrder.Language.completeTheory.mem_or_not_mem`：mem_or_not_mem (φ : L
.Sentence) : φ in L.completeTheory M ∨ φ.not in L.completeTheory M
-/
theorem isMaximal [Nonempty M] : (L.completeTheory M).IsMaximal :=
  ⟨isSatisfiable L M, mem_or_not_mem L M⟩
/-
**FirstOrder.Language.completeTheory.isComplete** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.completeTheory`。
形式化陈述：isComplete [Nonempty M] : (L.completeTheory M).IsComplete
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.IsMaximal.isComplete`：∀ {L : FirstOrder.Langu
age} {T : L.Theory}, T.IsMaximal → T.IsComplete
· 使用定理 `FirstOrder.Language.completeTheory.isMaximal`：isMaximal [Nonempty M] : (
L.completeTheory M).IsMaximal
-/
theorem isComplete [Nonempty M] : (L.completeTheory M).IsComplete :=
  (completeTheory.isMaximal L M).isComplete

end completeTheory

end Language

end FirstOrder

namespace Cardinal

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} (κ : Cardinal.{w}) (T : L.Theory)

/-- A theory is `κ`-categorical if all models of size `κ` are isomorphic. -/
/-
**Cardinal.Categorical** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：Categorical : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A theory is `κ`-categorical if all models of size `κ` are isomorphic.
-/
def Categorical : Prop :=
  ∀ M N : T.ModelType, #M = κ → #N = κ → Nonempty (M ≃[L] N)

/-- The Łoś–Vaught Test : a criterion for categorical theories to be complete. -/
/-
**Cardinal.Categorical.isComplete** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.Categorica
l`。
形式化陈述：∀ {L : FirstOrder.Language} (κ : Cardinal.{w}) (T : L.Theory),   κ.Categor
ical T →     Cardinal.aleph0 ≤ κ →       Cardinal.lift.{w, max u v} L.card ≤ Car
dinal.lift.{max u v, w} κ →         T.IsSatisfiable → (∀ (M : T.ModelType), Infi
nite ↑M) → T.IsComplete
参数：κ : Cardinal.{w}；T : L.Theory；∀ (M : T.ModelType), Infinite ↑M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.exists_model_card_eq`：exists_model_card_eq (h
 : exists M : ModelType.{u, v, max u v} T, Infinite M) (κ : Cardinal.{w}) (h1 : 
ℵ₀ <= κ) (h2 : Cardinal.lift.{w} L.ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Theory.models_sentence_iff`：models_sentence_iff {φ :
 L.Sentence} : T ⊨ᵇ φ ↔ forall M : ModelType.{u, v, max u v} T, M ⊨ φ
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `FirstOrder.Language.exists_elementarilyEquivalent_card_eq`：exists_elemen
tarilyEquivalent_card_eq (M : Type w') [L.Structure M] [Infinite M] (κ : Cardina
l.{w}) (h1 : ℵ₀ <= κ) (h2 : lift.{w} L.card <= …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `FirstOrder.Language.ElementarilyEquivalent.realize_sentence`：realize_sen
tence (h : M ≅[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ
· 使用定理 `FirstOrder.Language.StrongHomClass.realize_sentence`：realize_sentence (φ
 : L.Sentence) : M ⊨ φ ↔ N ⊨ φ
· 使用定理 `FirstOrder.Language.Equiv.instStrongHomClass`：∀ {L : FirstOrder.Language
} {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N],   
L.StrongHomClass (L.Equiv M N) M N
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `FirstOrder.Language.Sentence.realize_not`：realize_not : M ⊨ φ.not ↔ ¬M ⊨
 φ

--- 原说明 ---
The Łoś–Vaught Test : a criterion for categorical theories to be complete.
-/
theorem Categorical.isComplete (h : κ.Categorical T) (h1 : ℵ₀ ≤ κ)
    (h2 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) (hS : T.IsSatisfiable)
    (hT : ∀ M : Theory.ModelType.{u, v, max u v} T, Infinite M) : T.IsComplete :=
  ⟨hS, fun φ => by
    obtain ⟨_, _⟩ := Theory.exists_model_card_eq ⟨hS.some, hT hS.some⟩ κ h1 h2
    rw [Theory.models_sentence_iff, Theory.models_sentence_iff]
    by_contra! ⟨⟨MF, hMF⟩, MT, hMT⟩
    rw [Sentence.realize_not, Classical.not_not] at hMT
    refine hMF ?_
    have := hT MT
    have := hT MF
    obtain ⟨NT, MNT, hNT⟩ := exists_elementarilyEquivalent_card_eq L MT κ h1 h2
    obtain ⟨NF, MNF, hNF⟩ := exists_elementarilyEquivalent_card_eq L MF κ h1 h2
    obtain ⟨TF⟩ := h (MNT.toModel T) (MNF.toModel T) hNT hNF
    exact
      ((MNT.realize_sentence φ).trans
        ((StrongHomClass.realize_sentence TF φ).trans (MNF.realize_sentence φ).symm)).1 hMT⟩
/-
**Cardinal.empty_theory_categorical** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：empty_theory_categorical (T : Language.empty.Theory) : κ.Categorical T
参数：T : Language.empty.Theory。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.empty.nonempty_equiv_iff`：∀ {M : Type w} {N : Type w
'} [inst : FirstOrder.Language.empty.Structure M]   [inst_1 : FirstOrder.Languag
e.empty.Structure N],   Nonempty (…
-/
theorem empty_theory_categorical (T : Language.empty.Theory) : κ.Categorical T := fun M N hM hN =>
  by rw [empty.nonempty_equiv_iff, hM, hN]
/-
**Cardinal.empty_infinite_Theory_isComplete** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`
。
形式化陈述：empty_infinite_Theory_isComplete : Language.empty.infiniteTheory.IsComplet
e
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.Categorical.isComplete`：∀ {L : FirstOrder.Language} (κ : Cardin
al.{w}) (T : L.Theory),   κ.Categorical T →     Cardinal.aleph0 ≤ κ →       Card
inal.lift.{w, max u v…
· 使用定理 `Cardinal.empty_theory_categorical`：empty_theory_categorical (T : Languag
e.empty.Theory) : κ.Categorical T
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.card_empty`：card_empty : Language.empty.card = 0
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.model_infiniteTheory_iff`：model_infiniteTheory_iff :
 M ⊨ L.infiniteTheory ↔ Infinite M
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
-/
theorem empty_infinite_Theory_isComplete : Language.empty.infiniteTheory.IsComplete :=
  (empty_theory_categorical.{0} ℵ₀ _).isComplete ℵ₀ _ le_rfl (by simp)
    ⟨by
      haveI : Language.empty.Structure ℕ := emptyStructure
      exact ((model_infiniteTheory_iff Language.empty).2 (inferInstance : Infinite ℕ)).bundled⟩
    fun M => (model_infiniteTheory_iff Language.empty).1 M.is_model

end Cardinal

