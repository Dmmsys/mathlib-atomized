/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Ordinal.Family

/-!
# Enumerating sets of ordinals by ordinals

The ordinals have the peculiar property that every subset bounded above is a small type, while
themselves not being small. As a consequence of this, every unbounded subset of `Ordinal` is order
isomorphic to `Ordinal`.

We define this correspondence as `enumOrd`, and use it to then define an order isomorphism
`enumOrdOrderIso`.

This can be thought of as an ordinal analog of `Nat.nth`.
-/

@[expose] public section

universe u

open Order Set

namespace Ordinal

variable {o a b : Ordinal.{u}}

/-- Enumerator function for an unbounded set of ordinals.

The definition is an implementation detail; this function is entirely characterized by being an
order isomorphism. See `enumOrdOrderIso`. -/
@[no_expose]
/-
**Ordinal.enumOrd** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：enumOrd (s : Set Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u}
参数：s : Set Ordinal.{u}；o : Ordinal.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Enumerator function for an unbounded set of ordinals.

The definition is an implementation detail; this function is entirely characteri
zed by being an
order isomorphism. See `enumOrdOrderIso`.
-/
noncomputable def enumOrd (s : Set Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u} :=
  sInf (s ∩ { b | ∀ c, c < o → enumOrd s c < b })
termination_by o

variable {s : Set Ordinal.{u}}
/-
**Ordinal.enumOrd_le_of_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enumOrd_le_of_forall_lt (ha : a in s) (H : forall b < o, enumOrd s b < a) 
: enumOrd s o <= a
参数：ha : a in s；H : forall b < o, enumOrd s b < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Enum.0.Ordinal.enumOrd.eq_1`：∀ (s : S
et Ordinal.{u}) (o : Ordinal.{u}), Ordinal.enumOrd s o = sInf (s ∩ {b | ∀ c < o,
 Ordinal.enumOrd s c < b})
· 使用定理 `csInf_le'`：csInf_le' (h : a in s) : sInf s <= a
-/
theorem enumOrd_le_of_forall_lt (ha : a ∈ s) (H : ∀ b < o, enumOrd s b < a) : enumOrd s o ≤ a := by
  rw [enumOrd]
  exact csInf_le' ⟨ha, H⟩

/-- The set in the definition of `enumOrd` is nonempty. -/
/-
**Ordinal.enumOrd_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set in the definition of `enumOrd` is nonempty.
-/
private theorem enumOrd_nonempty (hs : ¬ BddAbove s) (o : Ordinal) :
    (s ∩ { b | ∀ c, c < o → enumOrd s c < b }).Nonempty := by
  rw [not_bddAbove_iff] at hs
  obtain ⟨a, ha⟩ := bddAbove_of_small (s := enumOrd s '' Iio o)
  obtain ⟨b, hb, hba⟩ := hs a
  exact ⟨b, hb, fun c hc ↦ (ha (mem_image_of_mem _ hc)).trans_lt hba⟩
/-
**Ordinal.enumOrd_mem_aux** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem enumOrd_mem_aux (hs : ¬ BddAbove s) (o : Ordinal) :
    enumOrd s o ∈ s ∩ { b | ∀ c, c < o → enumOrd s c < b } := by
  rw [enumOrd]
  exact csInf_mem (enumOrd_nonempty hs o)
/-
**Ordinal.enumOrd_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enumOrd_mem (hs : ¬ BddAbove s) (o : Ordinal) : enumOrd s o in s
参数：hs : ¬ BddAbove s；o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Enum.0.Ordinal.enumOrd_mem_aux`：∀ {s 
: Set Ordinal.{u}},   ¬BddAbove s → ∀ (o : Ordinal.{u}), Ordinal.enumOrd s o ∈ s
 ∩ {b | ∀ c < o, Ordinal.enumOrd s c < b}
-/
theorem enumOrd_mem (hs : ¬ BddAbove s) (o : Ordinal) : enumOrd s o ∈ s :=
  (enumOrd_mem_aux hs o).1
/-
**Ordinal.enumOrd_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enumOrd_strictMono (hs : ¬ BddAbove s) : StrictMono (enumOrd s)
参数：hs : ¬ BddAbove s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Enum.0.Ordinal.enumOrd_mem_aux`：∀ {s 
: Set Ordinal.{u}},   ¬BddAbove s → ∀ (o : Ordinal.{u}), Ordinal.enumOrd s o ∈ s
 ∩ {b | ∀ c < o, Ordinal.enumOrd s c < b}
-/
theorem enumOrd_strictMono (hs : ¬ BddAbove s) : StrictMono (enumOrd s) :=
  fun a b ↦ (enumOrd_mem_aux hs b).2 a
/-
**Ordinal.enumOrd_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enumOrd_injective (hs : ¬ BddAbove s) : Function.Injective (enumOrd s)
参数：hs : ¬ BddAbove s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Ordinal.enumOrd_strictMono`：enumOrd_strictMono (hs : ¬ BddAbove s) : Str
ictMono (enumOrd s)
-/
theorem enumOrd_injective (hs : ¬ BddAbove s) : Function.Injective (enumOrd s) :=
  (enumOrd_strictMono hs).injective
/-
**Ordinal.enumOrd_inj** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enumOrd_inj (hs : ¬ BddAbove s) {a b : Ordinal} : enumOrd s a = enumOrd s 
b ↔ a = b
参数：hs : ¬ BddAbove s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Ordinal.enumOrd_injective`：enumOrd_injective (hs : ¬ BddAbove s) : Funct
ion.Injective (enumOrd s)
-/
theorem enumOrd_inj (hs : ¬ BddAbove s) {a b : Ordinal} : enumOrd s a = enumOrd s b ↔ a = b :=
  (enumOrd_injective hs).eq_iff
/-
**Ordinal.enumOrd_le_enumOrd** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enumOrd_le_enumOrd (hs : ¬ BddAbove s) {a b : Ordinal} : enumOrd s a <= en
umOrd s b ↔ a <= b
参数：hs : ¬ BddAbove s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Ordinal.enumOrd_strictMono`：enumOrd_strictMono (hs : ¬ BddAbove s) : Str
ictMono (enumOrd s)
-/
theorem enumOrd_le_enumOrd (hs : ¬ BddAbove s) {a b : Ordinal} :
    enumOrd s a ≤ enumOrd s b ↔ a ≤ b :=
  (enumOrd_strictMono hs).le_iff_le
/-
**Ordinal.enumOrd_lt_enumOrd** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enumOrd_lt_enumOrd (hs : ¬ BddAbove s) {a b : Ordinal} : enumOrd s a < enu
mOrd s b ↔ a < b
参数：hs : ¬ BddAbove s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Ordinal.enumOrd_strictMono`：enumOrd_strictMono (hs : ¬ BddAbove s) : Str
ictMono (enumOrd s)
-/
theorem enumOrd_lt_enumOrd (hs : ¬ BddAbove s) {a b : Ordinal} :
    enumOrd s a < enumOrd s b ↔ a < b :=
  (enumOrd_strictMono hs).lt_iff_lt
/-
**Ordinal.id_le_enumOrd** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：id_le_enumOrd (hs : ¬ BddAbove s) : id <= enumOrd s
参数：hs : ¬ BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.id_le`：StrictMono.id_le [WellFoundedLT β] {f : β -> β} (hf : 
StrictMono f) : id <= f
· 使用定理 `Ordinal.enumOrd_strictMono`：enumOrd_strictMono (hs : ¬ BddAbove s) : Str
ictMono (enumOrd s)
-/
theorem id_le_enumOrd (hs : ¬ BddAbove s) : id ≤ enumOrd s :=
  (enumOrd_strictMono hs).id_le
/-
**Ordinal.le_enumOrd_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_enumOrd_self (hs : ¬ BddAbove s) {a} : a <= enumOrd s a
参数：hs : ¬ BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Ordinal.enumOrd_strictMono`：enumOrd_strictMono (hs : ¬ BddAbove s) : Str
ictMono (enumOrd s)
-/
theorem le_enumOrd_self (hs : ¬ BddAbove s) {a} : a ≤ enumOrd s a :=
  (enumOrd_strictMono hs).le_apply
/-
**Ordinal.enumOrd_succ_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enumOrd_succ_le (hs : ¬ BddAbove s) (ha : a in s) (hb : enumOrd s b < a) :
 enumOrd s (succ b) <= a
参数：hs : ¬ BddAbove s；ha : a in s；hb : enumOrd s b < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.enumOrd_le_of_forall_lt`：enumOrd_le_of_forall_lt (ha : a in s) (
H : forall b < o, enumOrd s b < a) : enumOrd s o <= a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Ordinal.enumOrd_strictMono`：enumOrd_strictMono (hs : ¬ BddAbove s) : Str
ictMono (enumOrd s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem enumOrd_succ_le (hs : ¬ BddAbove s) (ha : a ∈ s) (hb : enumOrd s b < a) :
    enumOrd s (succ b) ≤ a := by
  apply enumOrd_le_of_forall_lt ha
  intro c hc
  rw [lt_succ_iff] at hc
  exact ((enumOrd_strictMono hs).monotone hc).trans_lt hb
/-
**Ordinal.range_enumOrd** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：range_enumOrd (hs : ¬ BddAbove s) : range (enumOrd s) = s
参数：hs : ¬ BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Ordinal.enumOrd_mem`：enumOrd_mem (hs : ¬ BddAbove s) (o : Ordinal) : enu
mOrd s o in s
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Ordinal.enumOrd_le_of_forall_lt`：enumOrd_le_of_forall_lt (ha : a in s) (
H : forall b < o, enumOrd s b < a) : enumOrd s o <= a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `csInf_le'`：csInf_le' (h : a in s) : sInf s <= a
· 使用定理 `csInf_mem`：csInf_mem (hs : s.Nonempty) : sInf s in s
· 使用定理 `StrictMono.id_le`：StrictMono.id_le [WellFoundedLT β] {f : β -> β} (hf : 
StrictMono f) : id <= f
· 使用定理 `Ordinal.enumOrd_strictMono`：enumOrd_strictMono (hs : ¬ BddAbove s) : Str
ictMono (enumOrd s)
-/
theorem range_enumOrd (hs : ¬ BddAbove s) : range (enumOrd s) = s := by
  ext a
  let t := { b | a ≤ enumOrd s b }
  constructor
  · rintro ⟨b, rfl⟩
    exact enumOrd_mem hs b
  · intro ha
    refine ⟨sInf t, (enumOrd_le_of_forall_lt ha ?_).antisymm ?_⟩
    · intro b hb
      by_contra! hb'
      exact hb.not_ge (csInf_le' hb')
    · exact csInf_mem (s := t) ⟨a, (enumOrd_strictMono hs).id_le a⟩
/-
**Ordinal.enumOrd_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enumOrd_surjective (hs : ¬ BddAbove s) {b : Ordinal} (hb : b in s) : exist
s a, enumOrd s a = b
参数：hs : ¬ BddAbove s；hb : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.range_enumOrd`：range_enumOrd (hs : ¬ BddAbove s) : range (enumOr
d s) = s
-/
theorem enumOrd_surjective (hs : ¬ BddAbove s) {b : Ordinal} (hb : b ∈ s) :
    ∃ a, enumOrd s a = b := by
  rwa [← range_enumOrd hs] at hb
/-
**Ordinal.enumOrd_le_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enumOrd_le_of_subset {t : Set Ordinal} (hs : ¬ BddAbove s) (hst : s subset
eq t) : enumOrd t <= enumOrd s
参数：hs : ¬ BddAbove s；hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Enum.0.Ordinal.enumOrd.eq_1`：∀ (s : S
et Ordinal.{u}) (o : Ordinal.{u}), Ordinal.enumOrd s o = sInf (s ∩ {b | ∀ c < o,
 Ordinal.enumOrd s c < b})
· 使用定理 `csInf_le_csInf'`：csInf_le_csInf' {s t : Set α} (h₁ : t.Nonempty) (h₂ : t
 subseteq s) : sInf s <= sInf t
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Enum.0.Ordinal.enumOrd_nonempty`：∀ {s
 : Set Ordinal.{u}}, ¬BddAbove s → ∀ (o : Ordinal.{u}), (s ∩ {b | ∀ c < o, Ordin
al.enumOrd s c < b}).Nonempty
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.ofPred_subset_ofPred_of_imp`：∀ {α : Type u} {p q : α → Prop}, (∀ (a 
: α), p a → q a) → {a | p a} ⊆ {a | q a}
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用引理 `Mathlib.Tactic.GCongr.imp_mono`：imp_mono (h₁ : c -> a) (h₂ : c -> b -> d
) : (a -> b) -> c -> d
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem enumOrd_le_of_subset {t : Set Ordinal} (hs : ¬ BddAbove s) (hst : s ⊆ t) :
    enumOrd t ≤ enumOrd s := by
  intro a
  rw [enumOrd, enumOrd]
  gcongr with b c
  exacts [enumOrd_nonempty hs a, enumOrd_le_of_subset hs hst c]
termination_by a => a

/-- A characterization of `enumOrd`: it is the unique strict monotonic function with range `s`. -/
/-
**Ordinal.eq_enumOrd** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：eq_enumOrd (f : Ordinal -> Ordinal) (hs : ¬ BddAbove s) : enumOrd s = f ↔ 
StrictMono f ∧ range f = s
参数：f : Ordinal -> Ordinal；hs : ¬ BddAbove s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.enumOrd_strictMono`：enumOrd_strictMono (hs : ¬ BddAbove s) : Str
ictMono (enumOrd s)
· 使用定理 `Ordinal.range_enumOrd`：range_enumOrd (hs : ¬ BddAbove s) : range (enumOr
d s) = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StrictMono.range_inj`：StrictMono.range_inj [WellFoundedLT β] {f g : β ->
 γ} (hf : StrictMono f) (hg : StrictMono g) : Set.range f = Set.range g ↔ f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a

--- 原说明 ---
A characterization of `enumOrd`: it is the unique strict monotonic function with
 range `s`.
-/
theorem eq_enumOrd (f : Ordinal → Ordinal) (hs : ¬ BddAbove s) :
    enumOrd s = f ↔ StrictMono f ∧ range f = s := by
  constructor
  · rintro rfl
    exact ⟨enumOrd_strictMono hs, range_enumOrd hs⟩
  · rintro ⟨h₁, h₂⟩
    rwa [← (enumOrd_strictMono hs).range_inj h₁, range_enumOrd hs, eq_comm]
/-
**Ordinal.enumOrd_range** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enumOrd_range {f : Ordinal -> Ordinal} (hf : StrictMono f) : enumOrd (rang
e f) = f
参数：hf : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.eq_enumOrd`：eq_enumOrd (f : Ordinal -> Ordinal) (hs : ¬ BddAbove
 s) : enumOrd s = f ↔ StrictMono f ∧ range f = s
· 使用定理 `StrictMono.not_bddAbove_range_of_wellFoundedLT`：StrictMono.not_bddAbove_
range_of_wellFoundedLT {f : β -> β} [WellFoundedLT β] [NoMaxOrder β] (hf : Stric
tMono f) : ¬ BddAbove (Set.range f)
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem enumOrd_range {f : Ordinal → Ordinal} (hf : StrictMono f) : enumOrd (range f) = f :=
  (eq_enumOrd _ hf.not_bddAbove_range_of_wellFoundedLT).2 ⟨hf, rfl⟩

/-- If `s` is closed under nonempty suprema, then its enumerator function is normal.
See also `enumOrd_isNormal_iff_isClosed`. -/
/-
**Ordinal.isNormal_enumOrd** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isNormal_enumOrd (H : forall t subseteq s, t.Nonempty -> BddAbove t -> sSu
p t in s) (hs : ¬ BddAbove s) : IsNormal (enumOrd s)
参数：H : forall t subseteq s, t.Nonempty -> BddAbove t -> sSup t in s；hs : ¬ BddAb
ove s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.isNormal_iff`：isNormal_iff [LinearOrder α] [LinearOrder β] {f : α 
-> β} : IsNormal f ↔ StrictMono f ∧ forall o, IsSuccLimit o -> forall a, (forall
 b < o, …
· 使用定理 `Ordinal.enumOrd_strictMono`：enumOrd_strictMono (hs : ¬ BddAbove s) : Str
ictMono (enumOrd s)
· 使用定理 `Ordinal.enumOrd_le_of_forall_lt`：enumOrd_le_of_forall_lt (ha : a in s) (
H : forall b < o, enumOrd s b < a) : enumOrd s o <= a
· 使用定理 `Order.IsSuccLimit.bot_lt`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → ⊥ < a
· 使用定理 `Ordinal.enumOrd_mem`：enumOrd_mem (hs : ¬ BddAbove s) (o : Ordinal) : enu
mOrd s o in s
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
· 使用定理 `Order.IsSuccLimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : PartialOrd
er α] [inst_1 : SuccOrder α],   Order.IsSuccLimit b → a < b → Order.succ a < b
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
If `s` is closed under nonempty suprema, then its enumerator function is normal.
See also `enumOrd_isNormal_iff_isClosed`.
-/
theorem isNormal_enumOrd (H : ∀ t ⊆ s, t.Nonempty → BddAbove t → sSup t ∈ s) (hs : ¬ BddAbove s) :
    IsNormal (enumOrd s) := by
  refine isNormal_iff.2 ⟨enumOrd_strictMono hs, fun o ho a ha ↦ ?_⟩
  trans ⨆ b : Iio o, enumOrd s b
  · refine enumOrd_le_of_forall_lt ?_ (fun b hb ↦ (enumOrd_strictMono hs (lt_succ b)).trans_le ?_)
    · have : Nonempty (Iio o) := ⟨0, ho.bot_lt⟩
      apply H _ _ (range_nonempty _) bddAbove_of_small
      rintro _ ⟨c, rfl⟩
      exact enumOrd_mem hs c
    · exact Ordinal.le_iSup _ (⟨_, ho.succ_lt hb⟩ : Iio o)
  · exact Ordinal.iSup_le fun x ↦ ha _ x.2

@[simp]
/-
**Ordinal.enumOrd_univ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enumOrd_univ : enumOrd Set.univ = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Ordinal.enumOrd_range`：enumOrd_range {f : Ordinal -> Ordinal} (hf : Stri
ctMono f) : enumOrd (range f) = f
· 使用定理 `strictMono_id`：strictMono_id [Preorder α] : StrictMono (id : α -> α)
-/
theorem enumOrd_univ : enumOrd Set.univ = id := by
  rw [← range_id]
  exact enumOrd_range strictMono_id
/-
**Ordinal.enumOrd_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {s : Set Ordinal.{u}}, Ordinal.enumOrd s 0 = sInf s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Enum.0.Ordinal.enumOrd.eq_1`：∀ (s : S
et Ordinal.{u}) (o : Ordinal.{u}), Ordinal.enumOrd s o = sInf (s ∩ {b | ∀ c < o,
 Ordinal.enumOrd s c < b})
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma enumOrd_zero : enumOrd s 0 = sInf s := by rw [enumOrd]; simp

/-- An order isomorphism between an unbounded set of ordinals and the ordinals. -/
/-
**Ordinal.enumOrdOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：enumOrdOrderIso (s : Set Ordinal) (hs : ¬ BddAbove s) : Ordinal ≃o s
参数：s : Set Ordinal；hs : ¬ BddAbove s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.enumOrd_mem`：enumOrd_mem (hs : ¬ BddAbove s) (o : Ordinal) : enu
mOrd s o in s
· 使用定理 `Ordinal.enumOrd_strictMono`：enumOrd_strictMono (hs : ¬ BddAbove s) : Str
ictMono (enumOrd s)

--- 原说明 ---
An order isomorphism between an unbounded set of ordinals and the ordinals.
-/
noncomputable def enumOrdOrderIso (s : Set Ordinal) (hs : ¬ BddAbove s) : Ordinal ≃o s :=
  StrictMono.orderIsoOfSurjective (fun o => ⟨_, enumOrd_mem hs o⟩) (enumOrd_strictMono hs) fun s =>
    let ⟨a, ha⟩ := enumOrd_surjective hs s.prop
    ⟨a, Subtype.ext ha⟩

end Ordinal

