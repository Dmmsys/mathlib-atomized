/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.ElementarySubstructures

/-!
# Skolem Functions and Downward Löwenheim–Skolem

## Main Definitions

- `FirstOrder.Language.skolem₁` is a language consisting of Skolem functions for another language.

## Main Results

- `FirstOrder.Language.exists_elementarySubstructure_card_eq` is the Downward Löwenheim–Skolem
  theorem: If `s` is a set in an `L`-structure `M` and `κ` an infinite cardinal such that
  `max (#s, L.card) ≤ κ` and `κ ≤ # M`, then `M` has an elementary substructure containing `s` of
  cardinality `κ`.

## TODO

- Use `skolem₁` recursively to construct an actual Skolemization of a language.
-/

@[expose] public section


universe u v w w'

namespace FirstOrder

namespace Language

open Structure Cardinal

variable (L : Language.{u, v}) {M : Type w} [Nonempty M] [L.Structure M]

/-- A language consisting of Skolem functions for another language.
Called `skolem₁` because it is the first step in building a Skolemization of a language. -/
@[simps]
/-
**FirstOrder.Language.skolem** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A language consisting of Skolem functions for another language.
Called `skolem₁` because it is the first step in building a Skolemization of a l
anguage.
-/
def skolem₁ : Language :=
  ⟨fun n => L.BoundedFormula Empty (n + 1), fun _ => Empty⟩

variable {L}
/-
**FirstOrder.Language.card_functions_sum_skolem** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_functions_sum_skolem₁ :
    #(Σ n, (L.sum L.skolem₁).Functions n) = #(Σ n, L.BoundedFormula Empty (n + 1)) := by
  simp only [card_functions_sum, skolem₁_Functions, mk_sigma, sum_add_distrib']
  conv_lhs => enter [2, 1, i]; rw [lift_id'.{u, v}]
  rw [add_comm, add_eq_max, max_eq_left]
  · gcongr with n
    rw [← lift_le.{_, max u v}, lift_lift, lift_mk_le.{v}]
    refine ⟨⟨fun f => (func f default).bdEqual (func f default), fun f g h => ?_⟩⟩
    rcases h with ⟨rfl, ⟨rfl⟩⟩
    rfl
  · rw [← mk_sigma]
    exact infinite_iff.1 (Infinite.of_injective (fun n => ⟨n, ⊥⟩) fun x y xy =>
      (Sigma.mk.inj_iff.1 xy).1)
/-
**FirstOrder.Language.card_functions_sum_skolem** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_functions_sum_skolem₁_le : #(Σ n, (L.sum L.skolem₁).Functions n) ≤ max ℵ₀ L.card := by
  rw [card_functions_sum_skolem₁]
  trans #(Σ n, L.BoundedFormula Empty n)
  · exact
      ⟨⟨Sigma.map Nat.succ fun _ => id,
          Nat.succ_injective.sigma_map fun _ => Function.injective_id⟩⟩
  · refine _root_.trans BoundedFormula.card_le (lift_le.{max u v}.1 ?_)
    simp only [mk_empty, lift_zero, lift_uzero, zero_add]
    rfl

/-- The structure assigning each function symbol of `L.skolem₁` to a skolem function generated with
choice. -/
/-
**FirstOrder.Language.skolem** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure assigning each function symbol of `L.skolem₁` to a skolem function
 generated with
choice.
-/
noncomputable instance skolem₁Structure : L.skolem₁.Structure M :=
  ⟨fun {_} φ x => Classical.epsilon fun a => φ.Realize default (Fin.snoc x a : _ → M), fun {_} r =>
    Empty.elim r⟩

namespace Substructure

/-
**FirstOrder.Language.Substructure.skolem** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Substructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem skolem₁_reduct_isElementary (S : (L.sum L.skolem₁).Substructure M) :
    (LHom.sumInl.substructureReduct S).IsElementary := by
  apply (LHom.sumInl.substructureReduct S).isElementary_of_exists
  intro n φ x a h
  let φ' : (L.sum L.skolem₁).Functions n := LHom.sumInr.onFunction φ
  use ⟨funMap φ' ((↑) ∘ x), ?_⟩
  · exact Classical.epsilon_spec (p := fun a => BoundedFormula.Realize φ default
          (Fin.snoc (Subtype.val ∘ x) a)) ⟨a, h⟩
  · exact S.fun_mem (LHom.sumInr.onFunction φ) ((↑) ∘ x) (by
      exact fun i => (x i).2)

/-- Any `L.sum L.skolem₁`-substructure is an elementary `L`-substructure. -/
/-
**FirstOrder.Language.Substructure.elementarySkolem** 是 Mathlib 中的一个定义，位于命名空间 `F
irstOrder.Language.Substructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any `L.sum L.skolem₁`-substructure is an elementary `L`-substructure.
-/
noncomputable def elementarySkolem₁Reduct (S : (L.sum L.skolem₁).Substructure M) :
    L.ElementarySubstructure M :=
  ⟨LHom.sumInl.substructureReduct S, S.skolem₁_reduct_isElementary⟩
/-
**FirstOrder.Language.Substructure.coeSort_elementarySkolem** 是 Mathlib 中的一个定理，位
于命名空间 `FirstOrder.Language.Substructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeSort_elementarySkolem₁Reduct (S : (L.sum L.skolem₁).Substructure M) :
    (S.elementarySkolem₁Reduct : Type w) = S :=
  rfl

end Substructure

open Substructure

variable (L) (M)

/-
**FirstOrder.Language.Substructure.elementarySkolem** 是 Mathlib 中的一个实例，位于命名空间 `F
irstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Substructure.elementarySkolem₁Reduct.instSmall :
    Small.{max u v} (⊥ : (L.sum L.skolem₁).Substructure M).elementarySkolem₁Reduct := by
  rw [coeSort_elementarySkolem₁Reduct]
  infer_instance

omit [Nonempty M]
/-
**FirstOrder.Language.exists_small_elementarySubstructure** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language`。
形式化陈述：exists_small_elementarySubstructure : exists S : L.ElementarySubstructure 
M, Small.{max u v} S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Countable.toSmall`：∀ (α : Type v) [Countable α], Small.{w, v} α
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `FirstOrder.Language.Substructure.elementarySkolem₁Reduct.instSmall`：∀ (L
 : FirstOrder.Language) (M : Type w) [inst : Nonempty M] [inst_1 : L.Structure M
],   Small.{max u v, w} ↥⊥.elementarySkolem₁Reduct
-/
theorem exists_small_elementarySubstructure : ∃ S : L.ElementarySubstructure M, Small.{max u v} S :=
  (isEmpty_or_nonempty M).elim
    (fun _ => ⟨⊤, Countable.toSmall _⟩)
    (fun _ => ⟨Substructure.elementarySkolem₁Reduct ⊥, inferInstance⟩)

variable {M}

/-- The **Downward Löwenheim–Skolem theorem** :
  If `s` is a set in an `L`-structure `M` and `κ` an infinite cardinal such that
  `max (#s, L.card) ≤ κ` and `κ ≤ # M`, then `M` has an elementary substructure containing `s` of
  cardinality `κ`. -/
/-
**FirstOrder.Language.exists_elementarySubstructure_card_eq** 是 Mathlib 中的一个定理，位
于命名空间 `FirstOrder.Language`。
形式化陈述：exists_elementarySubstructure_card_eq (s : Set M) (κ : Cardinal.{w'}) (h1 
: ℵ₀ <= κ) (h2 : Cardinal.lift.{w'} #s <= Cardinal.lift.{w} κ) (h3 : Cardinal.li
ft.{w'} L.card <= Cardinal.lift.{max u v} κ) (h4 : Cardinal.lift.{w} κ <= Cardin
al.lift.{w'} #M) : exists S : L.ElementarySubstructure M, s subseteq S ∧ Cardina
l.lift.{w'} #S = Cardinal.lift.{w} κ
参数：s : Set M；κ : Cardinal.{w'}；h1 : ℵ₀ <= κ；h2 : Cardinal.lift.{w'} #s <= Cardin
al.lift.{w} κ；h3 : Cardinal.lift.{w'} L.card <= Cardinal.lift.{max u v} κ；h4 : C
ardinal.lift.{w} κ <= Cardinal.lift.{w'} #M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.le_mk_iff_exists_set`：le_mk_iff_exists_set {c : Cardinal} {α : 
Type u} : c <= #α ↔ exists p : Set α, #p = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonempty_ulift`：nonempty_ulift : Nonempty (ULift α) ↔ Nonempty α
· 使用定理 `Cardinal.mk_ne_zero_iff`：mk_ne_zero_iff {α : Type u} : #α != 0 ↔ Nonempt
y α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Cardinal.aleph0_pos`：aleph0_pos : 0 < ℵ₀
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.aleph0_le_lift`：aleph0_le_lift {c : Cardinal.{u}} : ℵ₀ <= lift.
{v} c ↔ ℵ₀ <= c
· 使用定理 `Cardinal.mk_subtype_le`：mk_subtype_le {α : Type u} (p : α -> Prop) : #(S
ubtype p) <= #α
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `FirstOrder.Language.Substructure.subset_closure`：subset_closure : s subs
eteq closure L s
· 使用定理 `Cardinal.mk_image_eq_lift`：mk_image_eq_lift {α : Type u} {β : Type v} (f
 : α -> β) (s : Set α) (h : Injective f) : lift.{u} #(f '' s) = lift.{v} #s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `FirstOrder.Language.Substructure.coeSort_elementarySkolem₁Reduct`：coeSor
t_elementarySkolem₁Reduct (S : (L.sum L.skolem₁).Substructure M) : (S.elementary
Skolem₁Reduct : Type w) = S
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `FirstOrder.Language.Substructure.lift_card_closure_le`：lift_card_closure
_le : Cardinal.lift.{u, w} #(closure L s) <= max ℵ₀ (Cardinal.lift.{u, w} #s + C
ardinal.lift.{w, u} #(Σ i, L.Functions i))
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
· 使用定理 `Cardinal.add_eq_max`：add_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) : a + b 
= max a b
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
The **Downward Löwenheim–Skolem theorem** :
  If `s` is a set in an `L`-structure `M` and `κ` an infinite cardinal such that
  `max (#s, L.card) ≤ κ` and `κ ≤ # M`, then `M` has an elementary substructure 
containing `s` of
  cardinality `κ`.
-/
theorem exists_elementarySubstructure_card_eq (s : Set M) (κ : Cardinal.{w'}) (h1 : ℵ₀ ≤ κ)
    (h2 : Cardinal.lift.{w'} #s ≤ Cardinal.lift.{w} κ)
    (h3 : Cardinal.lift.{w'} L.card ≤ Cardinal.lift.{max u v} κ)
    (h4 : Cardinal.lift.{w} κ ≤ Cardinal.lift.{w'} #M) :
    ∃ S : L.ElementarySubstructure M, s ⊆ S ∧ Cardinal.lift.{w'} #S = Cardinal.lift.{w} κ := by
  obtain ⟨s', hs'⟩ := Cardinal.le_mk_iff_exists_set.1 h4
  rw [← aleph0_le_lift.{_, w}] at h1
  rw [← hs'] at h1 h2 ⊢
  have : Nonempty M := nonempty_ulift.1 (Cardinal.mk_ne_zero_iff.1
    (aleph0_pos.trans_le (h1.trans (Cardinal.mk_subtype_le _))).ne')
  refine
    ⟨elementarySkolem₁Reduct (closure (L.sum L.skolem₁) (s ∪ Equiv.ulift '' s')),
      (s.subset_union_left).trans subset_closure, ?_⟩
  have h := mk_image_eq_lift _ s' Equiv.ulift.injective
  rw [lift_umax.{w, w'}, lift_id'.{w, w'}] at h
  rw [coeSort_elementarySkolem₁Reduct, ← h, lift_inj]
  refine
    le_antisymm (lift_le.1 (lift_card_closure_le.trans ?_))
      (mk_le_mk_of_subset ((s.subset_union_right).trans subset_closure))
  rw [max_le_iff, aleph0_le_lift, ← aleph0_le_lift.{_, w'}, h, add_eq_max, max_le_iff, lift_le]
  · refine ⟨h1, (mk_union_le _ _).trans ?_, (lift_le.2 card_functions_sum_skolem₁_le).trans ?_⟩
    · rw [← lift_le, lift_add, h, add_comm, add_eq_max h1]
      exact max_le le_rfl h2
    · rw [lift_max, lift_aleph0, max_le_iff, aleph0_le_lift, and_comm, ← lift_le.{w'},
        lift_lift, lift_lift, ← aleph0_le_lift, h]
      refine ⟨?_, h1⟩
      rw [← lift_lift.{w', w}]
      refine _root_.trans (lift_le.{w}.2 h3) ?_
      rw [lift_lift, ← lift_lift.{w, max u v}, ← hs', ← h, lift_lift]
  · refine _root_.trans ?_ (lift_le.2 (mk_le_mk_of_subset Set.subset_union_right))
    rw [aleph0_le_lift, ← aleph0_le_lift, h]
    exact h1

end Language

end FirstOrder

