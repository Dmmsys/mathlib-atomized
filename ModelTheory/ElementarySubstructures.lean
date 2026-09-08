/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.ElementaryMaps
public import Mathlib.ModelTheory.Definability

/-!
# Elementary Substructures

## Main Definitions

- A `FirstOrder.Language.ElementarySubstructure` is a substructure where the realization of each
  formula agrees with the realization in the larger model.

## Main Results

- The Tarski-Vaught Test for substructures:
  `FirstOrder.Language.Substructure.isElementary_of_exists` gives a simple criterion for a
  substructure to be elementary.
-/

@[expose] public section


open FirstOrder

namespace FirstOrder

namespace Language

open Structure

variable {L : Language} {M : Type*} [L.Structure M]

/-- A substructure is elementary when every formula applied to a tuple in the substructure
  agrees with its value in the overall structure. -/
/-
**FirstOrder.Language.Substructure.IsElementary** 是 Mathlib 中的一个定义，位于命名空间 `First
Order.Language.Substructure`。
形式化陈述：{L : FirstOrder.Language} → {M : Type u_1} → [inst : L.Structure M] → L.Su
bstructure M → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A substructure is elementary when every formula applied to a tuple in the substr
ucture
  agrees with its value in the overall structure.
-/
def Substructure.IsElementary (S : L.Substructure M) : Prop :=
  ∀ ⦃n⦄ (φ : L.Formula (Fin n)) (x : Fin n → S), φ.Realize (((↑) : _ → M) ∘ x) ↔ φ.Realize x

variable (L M)

/-- An elementary substructure is one in which every formula applied to a tuple in the substructure
  agrees with its value in the overall structure. -/
/-
**FirstOrder.Language.ElementarySubstructure** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstO
rder.Language`。
形式化陈述：(L : FirstOrder.Language) → (M : Type u_1) → [L.Structure M] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An elementary substructure is one in which every formula applied to a tuple in t
he substructure
  agrees with its value in the overall structure.
-/
structure ElementarySubstructure where
  /-- The underlying substructure -/
  toSubstructure : L.Substructure M
  isElementary' : toSubstructure.IsElementary

variable {L M}

namespace ElementarySubstructure

attribute [coe] toSubstructure

/-
**FirstOrder.Language.ElementarySubstructure.instCoe** 是 Mathlib 中的一个实例，位于命名空间 `
FirstOrder.Language.ElementarySubstructure`。
形式化陈述：instCoe : Coe (L.ElementarySubstructure M) (L.Substructure M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoe : Coe (L.ElementarySubstructure M) (L.Substructure M) :=
  ⟨ElementarySubstructure.toSubstructure⟩
/-
**FirstOrder.Language.ElementarySubstructure.instSetLike** 是 Mathlib 中的一个实例，位于命名
空间 `FirstOrder.Language.ElementarySubstructure`。
形式化陈述：instSetLike : SetLike (L.ElementarySubstructure M) M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSetLike : SetLike (L.ElementarySubstructure M) M :=
  ⟨fun x => x.toSubstructure.carrier, fun ⟨⟨s, hs1⟩, hs2⟩ ⟨⟨t, ht1⟩, _⟩ _ => by
    congr⟩
/-
**FirstOrder.Language.ElementarySubstructure.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOr
der.Language.ElementarySubstructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (L.ElementarySubstructure M) := .ofSetLike (L.ElementarySubstructure M) M
/-
**FirstOrder.Language.ElementarySubstructure.inducedStructure** 是 Mathlib 中的一个实例
，位于命名空间 `FirstOrder.Language.ElementarySubstructure`。
形式化陈述：inducedStructure (S : L.ElementarySubstructure M) : L.Structure S
参数：S : L.ElementarySubstructure M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inducedStructure (S : L.ElementarySubstructure M) : L.Structure S :=
  Substructure.inducedStructure

@[simp]
/-
**FirstOrder.Language.ElementarySubstructure.isElementary** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language.ElementarySubstructure`。
形式化陈述：isElementary (S : L.ElementarySubstructure M) : (S : L.Substructure M).IsE
lementary
参数：S : L.ElementarySubstructure M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.ElementarySubstructure.isElementary'`：∀ {L : FirstOr
der.Language} {M : Type u_1} [inst : L.Structure M] (self : L.ElementarySubstruc
ture M),   (↑self).IsElementary
-/
theorem isElementary (S : L.ElementarySubstructure M) : (S : L.Substructure M).IsElementary :=
  S.isElementary'

/-- The natural embedding of an `L.Substructure` of `M` into `M`. -/
/-
**FirstOrder.Language.ElementarySubstructure.subtype** 是 Mathlib 中的一个定义，位于命名空间 `
FirstOrder.Language.ElementarySubstructure`。
形式化陈述：subtype (S : L.ElementarySubstructure M) : S ↪ₑ[L] M where toFun
参数：S : L.ElementarySubstructure M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.ElementarySubstructure.isElementary`：isElementary (S
 : L.ElementarySubstructure M) : (S : L.Substructure M).IsElementary

--- 原说明 ---
The natural embedding of an `L.Substructure` of `M` into `M`.
-/
def subtype (S : L.ElementarySubstructure M) : S ↪ₑ[L] M where
  toFun := (↑)
  map_formula' := S.isElementary

@[simp]
/-
**FirstOrder.Language.ElementarySubstructure.subtype_apply** 是 Mathlib 中的一个定理，位于
命名空间 `FirstOrder.Language.ElementarySubstructure`。
形式化陈述：subtype_apply {S : L.ElementarySubstructure M} {x : S} : subtype S x = x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_apply {S : L.ElementarySubstructure M} {x : S} : subtype S x = x :=
  rfl
/-
**FirstOrder.Language.ElementarySubstructure.subtype_injective** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language.ElementarySubstructure`。
形式化陈述：subtype_injective (S : L.ElementarySubstructure M) : Function.Injective (s
ubtype S)
参数：S : L.ElementarySubstructure M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem subtype_injective (S : L.ElementarySubstructure M) : Function.Injective (subtype S) :=
  Subtype.coe_injective

@[simp]
/-
**FirstOrder.Language.ElementarySubstructure.coe_subtype** 是 Mathlib 中的一个定理，位于命名
空间 `FirstOrder.Language.ElementarySubstructure`。
形式化陈述：coe_subtype (S : L.ElementarySubstructure M) : ⇑S.subtype = Subtype.val
参数：S : L.ElementarySubstructure M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype (S : L.ElementarySubstructure M) : ⇑S.subtype = Subtype.val :=
  rfl

/-- The substructure `M` of the structure `M` is elementary. -/
/-
**FirstOrder.Language.ElementarySubstructure.instTop** 是 Mathlib 中的一个实例，位于命名空间 `
FirstOrder.Language.ElementarySubstructure`。
形式化陈述：instTop : Top (L.ElementarySubstructure M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The substructure `M` of the structure `M` is elementary.
-/
instance instTop : Top (L.ElementarySubstructure M) :=
  ⟨⟨⊤, fun _ _ _ => Substructure.realize_formula_top.symm⟩⟩
/-
**FirstOrder.Language.ElementarySubstructure.instInhabited** 是 Mathlib 中的一个实例，位于
命名空间 `FirstOrder.Language.ElementarySubstructure`。
形式化陈述：instInhabited : Inhabited (L.ElementarySubstructure M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (L.ElementarySubstructure M) :=
  ⟨⊤⟩

@[simp]
/-
**FirstOrder.Language.ElementarySubstructure.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.ElementarySubstructure`。
形式化陈述：mem_top (x : M) : x in (⊤ : L.ElementarySubstructure M)
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_top (x : M) : x ∈ (⊤ : L.ElementarySubstructure M) :=
  Set.mem_univ x

@[simp]
/-
**FirstOrder.Language.ElementarySubstructure.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.ElementarySubstructure`。
形式化陈述：coe_top : ((⊤ : L.ElementarySubstructure M) : Set M) = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ((⊤ : L.ElementarySubstructure M) : Set M) = Set.univ :=
  rfl

@[simp]
/-
**FirstOrder.Language.ElementarySubstructure.realize_sentence** 是 Mathlib 中的一个定理
，位于命名空间 `FirstOrder.Language.ElementarySubstructure`。
形式化陈述：realize_sentence (S : L.ElementarySubstructure M) (φ : L.Sentence) : S ⊨ φ
 ↔ M ⊨ φ
参数：S : L.ElementarySubstructure M；φ : L.Sentence。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.map_sentence`：map_sentence (f : 
M ↪ₑ[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ
-/
theorem realize_sentence (S : L.ElementarySubstructure M) (φ : L.Sentence) : S ⊨ φ ↔ M ⊨ φ :=
  S.subtype.map_sentence φ

@[simp]
/-
**FirstOrder.Language.ElementarySubstructure.theory_model_iff** 是 Mathlib 中的一个定理
，位于命名空间 `FirstOrder.Language.ElementarySubstructure`。
形式化陈述：theory_model_iff (S : L.ElementarySubstructure M) (T : L.Theory) : S ⊨ T ↔
 M ⊨ T
参数：S : L.ElementarySubstructure M；T : L.Theory。
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
theorem theory_model_iff (S : L.ElementarySubstructure M) (T : L.Theory) : S ⊨ T ↔ M ⊨ T := by
  simp only [Theory.model_iff, realize_sentence]
/-
**FirstOrder.Language.ElementarySubstructure.theory_model** 是 Mathlib 中的一个实例，位于命
名空间 `FirstOrder.Language.ElementarySubstructure`。
形式化陈述：theory_model {T : L.Theory} [h : M ⊨ T] {S : L.ElementarySubstructure M} :
 S ⊨ T
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.ElementarySubstructure.theory_model_iff`：theory_mode
l_iff (S : L.ElementarySubstructure M) (T : L.Theory) : S ⊨ T ↔ M ⊨ T
-/
instance theory_model {T : L.Theory} [h : M ⊨ T] {S : L.ElementarySubstructure M} : S ⊨ T :=
  (theory_model_iff S T).2 h
/-
**FirstOrder.Language.ElementarySubstructure.instNonempty** 是 Mathlib 中的一个实例，位于命
名空间 `FirstOrder.Language.ElementarySubstructure`。
形式化陈述：instNonempty [Nonempty M] {S : L.ElementarySubstructure M} : Nonempty S
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.model_nonemptyTheory_iff`：model_nonemptyTheory_iff :
 M ⊨ L.nonemptyTheory ↔ Nonempty M
-/
instance instNonempty [Nonempty M] {S : L.ElementarySubstructure M} : Nonempty S :=
  (model_nonemptyTheory_iff L).1 inferInstance
/-
**FirstOrder.Language.ElementarySubstructure.elementarilyEquivalent** 是 Mathlib 
中的一个定理，位于命名空间 `FirstOrder.Language.ElementarySubstructure`。
形式化陈述：elementarilyEquivalent (S : L.ElementarySubstructure M) : S ≅[L] M
参数：S : L.ElementarySubstructure M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.elementarilyEquivalent`：elementa
rilyEquivalent (f : M ↪ₑ[L] N) : M ≅[L] N
-/
theorem elementarilyEquivalent (S : L.ElementarySubstructure M) : S ≅[L] M :=
  S.subtype.elementarilyEquivalent

end ElementarySubstructure

namespace Substructure

/-- The Tarski-Vaught test for elementarity of a substructure. -/
/-
**FirstOrder.Language.Substructure.isElementary_of_exists** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language.Substructure`。
形式化陈述：isElementary_of_exists (S : L.Substructure M) (htv : forall (n : Nat) (φ :
 L.BoundedFormula Empty (n + 1)) (x : Fin n -> S) (a : M), φ.Realize default (Fi
n.snoc ((↑) ∘ x) a : _ -> M) -> exists b : S, φ.Realize default (Fin.snoc ((↑) ∘
 x) b : _ -> M)) : S.IsElementary
参数：S : L.Substructure M；htv : forall (n : Nat) (φ : L.BoundedFormula Empty (n + 
1)) (x : Fin n -> S) (a : M), φ.Realize default (Fin.snoc ((↑) ∘ x) a : _ -> M) 
-> exists b : S, φ.Realize default (Fin.snoc ((↑) ∘ x) b : _ -> M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Embedding.isElementary_of_exists`：isElementary_of_ex
ists (f : M ↪[L] N) (htv : forall (n : Nat) (φ : L.BoundedFormula Empty (n + 1))
 (x : Fin n -> M) (a : N), φ.Realize defau…

--- 原说明 ---
The Tarski-Vaught test for elementarity of a substructure.
-/
theorem isElementary_of_exists (S : L.Substructure M)
    (htv :
      ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → S) (a : M),
        φ.Realize default (Fin.snoc ((↑) ∘ x) a : _ → M) →
          ∃ b : S, φ.Realize default (Fin.snoc ((↑) ∘ x) b : _ → M)) :
    S.IsElementary := fun _ => S.subtype.isElementary_of_exists htv

/-- Bundles a substructure satisfying the Tarski-Vaught test as an elementary substructure. -/
@[simps]
/-
**FirstOrder.Language.Substructure.toElementarySubstructure** 是 Mathlib 中的一个定义，位
于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：toElementarySubstructure (S : L.Substructure M) (htv : forall (n : Nat) (φ
 : L.BoundedFormula Empty (n + 1)) (x : Fin n -> S) (a : M), φ.Realize default (
Fin.snoc ((↑) ∘ x) a : _ -> M) -> exists b : S, φ.Realize default (Fin.snoc ((↑)
 ∘ x) b : _ -> M)) : L.ElementarySubstructure M
参数：S : L.Substructure M；htv : forall (n : Nat) (φ : L.BoundedFormula Empty (n + 
1)) (x : Fin n -> S) (a : M), φ.Realize default (Fin.snoc ((↑) ∘ x) a : _ -> M) 
-> exists b : S, φ.Realize default (Fin.snoc ((↑) ∘ x) b : _ -> M)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.isElementary_of_exists`：isElementary_of
_exists (S : L.Substructure M) (htv : forall (n : Nat) (φ : L.BoundedFormula Emp
ty (n + 1)) (x : Fin n -> S) (a : M), φ.Reali…

--- 原说明 ---
Bundles a substructure satisfying the Tarski-Vaught test as an elementary substr
ucture.
-/
def toElementarySubstructure (S : L.Substructure M)
    (htv :
      ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → S) (a : M),
        φ.Realize default (Fin.snoc ((↑) ∘ x) a : _ → M) →
          ∃ b : S, φ.Realize default (Fin.snoc ((↑) ∘ x) b : _ → M)) :
    L.ElementarySubstructure M :=
  ⟨S, S.isElementary_of_exists htv⟩

end Substructure

/-- A set meets definable sets if it meets every nonempty definable subset. -/
/-
**FirstOrder.Language.MeetsDefinable** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age`。
形式化陈述：MeetsDefinable (A : Set M) : Prop
参数：A : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set meets definable sets if it meets every nonempty definable subset.
-/
def MeetsDefinable (A : Set M) : Prop :=
  ∀ (D : Set M), D.Nonempty → A.Definable₁ L D → (D ∩ A).Nonempty

namespace MeetsDefinable

open Set Substructure

variable {A : Set M}

/-- The closure of a set meeting definable sets is equal to itself. -/
/-
**FirstOrder.Language.MeetsDefinable.closure_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.MeetsDefinable`。
形式化陈述：closure_eq_self (hA : L.MeetsDefinable A) : closure L A = A
参数：hA : L.MeetsDefinable A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Substructure.coe_closure_eq_range_term_realize`：coe_
closure_eq_range_term_realize : (closure L s : Set M) = range (@Term.realize L _
 _ _ ((↑) : s -> M))
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `FirstOrder.Language.Term.realize_varsToConstants`：realize_varsToConstant
s [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M] {t : L.Term (α 
oplus β)} {v : β -> M} : t.varsToConst…
· 使用定理 `FirstOrder.Language.Term.realize_relabel`：realize_relabel {t : L.Term α}
 {g : α -> β} {v : β -> M} : (t.relabel g).realize v = t.realize (v ∘ g)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.singleton_inter_nonempty`：singleton_inter_nonempty : ({a} inter s).N
onempty ↔ a in s
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `FirstOrder.Language.Substructure.subset_closure`：subset_closure : s subs
eteq closure L s

--- 原说明 ---
The closure of a set meeting definable sets is equal to itself.
-/
theorem closure_eq_self (hA : L.MeetsDefinable A) :
    closure L A = A := by
  refine Subset.antisymm ?_ subset_closure
  rw [coe_closure_eq_range_term_realize]
  intro x hx
  have : A.Definable₁ L {x} := by
    obtain ⟨t, rfl⟩ := hx
    use (Term.var 0).equal (t.relabel Sum.inl).varsToConstants
    simp [Set.ext_iff]
  exact singleton_inter_nonempty.mp <| hA _ (singleton_nonempty x) this

/-- The closure of a set meeting definable sets is an elementary substructure. -/
/-
**FirstOrder.Language.MeetsDefinable.isElementary_closure** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language.MeetsDefinable`。
形式化陈述：isElementary_closure (hA : L.MeetsDefinable A) : (closure L A).IsElementar
y
参数：hA : L.MeetsDefinable A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.isElementary_of_exists`：isElementary_of
_exists (S : L.Substructure M) (htv : forall (n : Nat) (φ : L.BoundedFormula Emp
ty (n + 1)) (x : Fin n -> S) (a : M), φ.Reali…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.MeetsDefinable.closure_eq_self`：closure_eq_self (hA 
: L.MeetsDefinable A) : closure L A = A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.cast_refl`：∀ (n : ℕ) (h : n = n), Fin.cast h = id
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Fin.natAdd_zero`：∀ {n : ℕ}, Fin.natAdd 0 = Fin.cast ⋯
· 使用定理 `FirstOrder.Language.Formula.Realize.eq_1`：∀ {L : FirstOrder.Language} {M
 : Type w} [inst : L.Structure M] {α : Type u'} (φ : L.Formula α) (v : α → M),  
 φ.Realize v = FirstOrder.Lang…
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_toFormula`：realize_toFormula 
(φ : L.BoundedFormula α n) (v : α oplus (Fin n) -> M) : φ.toFormula.Realize v ↔ 
φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr)
· 使用定理 `FirstOrder.Language.LHom.realize_onBoundedFormula`：realize_onBoundedForm
ula [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M] {n : Nat} (ψ : L.Bounded
Formula α n) {v : α -> M} {xs : Fin n -…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForallOfFastIsEmpty`：∀ {α : Sort u} [inst 
: Meta.FastIsEmpty α] {β : α → Sort v}, Meta.FastSubsingleton ((x : α) → β x)
· 使用定理 `Lean.Meta.instFastIsEmptyEmpty`：Meta.FastIsEmpty Empty
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `Fin.lastCases_last`：∀ {n : ℕ} {motive : Fin (n + 1) → Sort u_1} {last : 
motive (Fin.last n)} {cast : (i : Fin n) → motive i.castSucc},   Fin.lastCases l
ast cast…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Fin.lastCases_castSucc`：∀ {n : ℕ} {motive : Fin (n + 1) → Sort u_1} {las
t : motive (Fin.last n)} {cast : (i : Fin n) → motive i.castSucc}   (i : Fin n),
 Fin.lastCas…
· 使用定理 `FirstOrder.Language.Term.realize_constants`：realize_constants {c : L.Con
stants} {v : α -> M} : c.term.realize v = c

--- 原说明 ---
The closure of a set meeting definable sets is an elementary substructure.
-/
theorem isElementary_closure (hA : L.MeetsDefinable A) :
    (closure L A).IsElementary := by
  refine isElementary_of_exists ((closure L).toFun A) ?_
  intro n φ x a hφ
  let D : Set M := {y : M | φ.Realize default (Fin.snoc (Subtype.val ∘ x) y)}
  have hD_ne : D.Nonempty := ⟨a,hφ⟩
  have hD : A.Definable₁ L D := by
    simp only [Definable₁, Definable, Fin.isValue]
    refine ⟨((L.lhomWithConstants A).onBoundedFormula φ).toFormula.relabel
      (Sum.elim Empty.elim id) |>.subst fun i => Fin.lastCases (Term.var 0)
        (fun j => (L.con ⟨x j, by
        nth_rw 1 [← hA.closure_eq_self]
        simp only [Subtype.coe_prop]
        ⟩).term) i, ?_⟩
    ext v
    simp only [Fin.isValue, mem_ofPred_eq, Formula.relabel, Formula.Realize,
      BoundedFormula.realize_subst, BoundedFormula.realize_relabel, Nat.add_zero, Fin.castAdd_zero,
      Fin.cast_refl, Function.comp_id, Fin.natAdd_zero, D]
    rw [← Formula.Realize, BoundedFormula.realize_toFormula, LHom.realize_onBoundedFormula]
    congr! 1
    ext i; cases i using Fin.lastCases <;> simp
  obtain ⟨b, hbD, hbA⟩ := hA D hD_ne hD
  exact ⟨⟨b, by rwa [← hA.closure_eq_self] at hbA⟩, hbD⟩

/-- Bundles the closure of a set meeting definable sets as an elementary substructure. -/
/-
**FirstOrder.Language.MeetsDefinable.toElementarySubstructure** 是 Mathlib 中的一个定义
，位于命名空间 `FirstOrder.Language.MeetsDefinable`。
形式化陈述：toElementarySubstructure (hA : L.MeetsDefinable A) : L.ElementarySubstruct
ure M
参数：hA : L.MeetsDefinable A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.MeetsDefinable.isElementary_closure`：isElementary_cl
osure (hA : L.MeetsDefinable A) : (closure L A).IsElementary

--- 原说明 ---
Bundles the closure of a set meeting definable sets as an elementary substructur
e.
-/
def toElementarySubstructure (hA : L.MeetsDefinable A) :
    L.ElementarySubstructure M :=
  ⟨closure L A, hA.isElementary_closure⟩

end MeetsDefinable

namespace ElementarySubstructure

open Set Formula

/-- An elementary substructure, regarded as a subset of the ambient structure, meets definable
sets. -/
/-
**FirstOrder.Language.ElementarySubstructure.meetsDefinable** 是 Mathlib 中的一个定理，位
于命名空间 `FirstOrder.Language.ElementarySubstructure`。
形式化陈述：meetsDefinable (S : L.ElementarySubstructure M) : L.MeetsDefinable (S : Se
t M)
参数：S : L.ElementarySubstructure M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `FirstOrder.Language.Formula.realize_equivSentence_symm_con`：realize_equi
vSentence_symm_con [L[[α]].Structure M] [(L.lhomWithConstants α).IsExpansionOn M
] (φ : L[[α]].Sentence) : ((equivSentence.symm φ…
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.map_formula`：map_formula (f : M 
↪ₑ[L] N) {α : Type*} (φ : L.Formula α) (x : α -> M) : φ.Realize (f ∘ x) ↔ φ.Real
ize x
· 使用定理 `FirstOrder.Language.Formula.realize_equivSentence_symm`：realize_equivSen
tence_symm (φ : L[[α]].Sentence) (v : α -> M) : (equivSentence.symm φ).Realize v
 ↔ @Sentence.Realize _ M (@Language.withCons…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForallOfFastIsEmpty`：∀ {α : Sort u} [inst 
: Meta.FastIsEmpty α] {β : α → Sort v}, Meta.FastSubsingleton ((x : α) → β x)
· 使用定理 `Lean.Meta.instFastIsEmptyFinOfNatNat`：Meta.FastIsEmpty (Fin 0)
· 使用定理 `FirstOrder.Language.ElementaryEmbedding.map_boundedFormula`：map_boundedF
ormula (f : M ↪ₑ[L] N) {α : Type*} {n : Nat} (φ : L.BoundedFormula α n) (v : α -
> M) (xs : Fin n -> M) : φ.Realize (f ∘ v) (f ∘ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
An elementary substructure, regarded as a subset of the ambient structure, meets
 definable
sets.
-/
theorem meetsDefinable (S : L.ElementarySubstructure M) : L.MeetsDefinable (S : Set M) := by
  rintro D ⟨x, hx⟩ ⟨φ, hφ⟩
  have hφx : φ.Realize ![x] := by
    simp [Set.ext_iff] at hφ
    simp [← hφ, hx]
  let ψ : L[[(S : Set M)]].Sentence := (φ.relabel Sum.inr).iExs
  have hψM : ψ.Realize M := by
    simpa only [Sentence.Realize, SetLike.coe_sort_coe, Formula.realize_iExs,
      Formula.realize_relabel, Sum.elim_comp_inr, ψ] using
        (⟨![x], hφx⟩ : ∃ w : Fin 1 → M, φ.Realize w)
  have hψS : ψ.Realize S := by
    rwa [← Formula.realize_equivSentence_symm_con, ← S.subtype.map_formula,
      Formula.realize_equivSentence_symm]
  simp only [Sentence.Realize, SetLike.coe_sort_coe, Formula.realize_iExs,
    Formula.realize_relabel, Sum.elim_comp_inr, ψ] at hψS
  obtain ⟨v', hv'⟩ := hψS
  refine ⟨v' 0, ?_, by simp⟩
  have hv'' : φ.Realize (Subtype.val ∘ v') := by
    simp only [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv,
      ← S.subtype.map_boundedFormula] at hv'
    simp only [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv]
    convert! hv' using 1
    funext i
    cases i <;> rfl
  change (Subtype.val ∘ v') ∈ {x | x 0 ∈ D}
  simpa [hφ] using hv''

end ElementarySubstructure

end Language

end FirstOrder

