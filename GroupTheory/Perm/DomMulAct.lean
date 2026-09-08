/-
Copyright (c) 2023 Junyan Xu, Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# Subgroup of `Equiv.Perm α` preserving a function

Let `α` and `ι` by types and let `f : α → ι`

* `DomMulAct.mem_stabilizer_iff` proves that the stabilizer of `f : α → ι`
  in `(Equiv.Perm α)ᵈᵐᵃ` is the set of `g : (Equiv.Perm α)ᵈᵐᵃ` such that `f ∘ (mk.symm g) = f`.

  The natural equivalence from `stabilizer (Perm α)ᵈᵐᵃ f` to `{ g : Perm α // p ∘ g = f }`
  can be obtained as `subtypeEquiv mk.symm (fun _ => mem_stabilizer_iff)`

* `DomMulAct.stabilizerMulEquiv` is the `MulEquiv` from
  the MulOpposite of this stabilizer to the product,
  for `i : ι`, of `Equiv.Perm {a // f a = i}`.

* Under `Fintype α` and `Fintype ι`, `DomMulAct.stabilizer_card p` computes
  the cardinality of the type of permutations preserving `p` :
  `Fintype.card {g : Perm α // f ∘ g = f} = ∏ i, (Fintype.card {a // f a = i})!`.

* Without `Fintype ι`, `DomMulAct.stabilizer_card' p` gives an equivalent
  formula, where the product is restricted to `Finset.univ.image f`.
-/

@[expose] public section

assert_not_exists Field

open Equiv MulAction

variable {α ι : Type*} {f : α → ι}

namespace DomMulAct

/-
**DomMulAct.mem_stabilizer_iff** 是 Mathlib 中的一个引理，位于命名空间 `DomMulAct`。
形式化陈述：mem_stabilizer_iff {g : (Perm α)ᵈᵐᵃ} : g in stabilizer (Perm α)ᵈᵐᵃ f ↔ f ∘
 (mk.symm g :) = f
参数：Perm α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_stabilizer_iff {g : (Perm α)ᵈᵐᵃ} :
    g ∈ stabilizer (Perm α)ᵈᵐᵃ f ↔ f ∘ (mk.symm g :) = f := by
  simp only [MulAction.mem_stabilizer_iff]; rfl

/-- The `invFun` component of `MulEquiv` from `MulAction.stabilizer (Perm α) f`
  to the product of the `Equiv.Perm {a // f a = i}`. -/
/-
**DomMulAct.stabilizerEquiv_invFun** 是 Mathlib 中的一个定义，位于命名空间 `DomMulAct`。
形式化陈述：stabilizerEquiv_invFun (g : forall i, Perm {a // f a = i}) (a : α) : α
参数：g : forall i, Perm {a // f a = i}；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `invFun` component of `MulEquiv` from `MulAction.stabilizer (Perm α) f`
  to the product of the `Equiv.Perm {a // f a = i}`.
-/
def stabilizerEquiv_invFun (g : ∀ i, Perm {a // f a = i}) (a : α) : α := g (f a) ⟨a, rfl⟩
/-
**DomMulAct.stabilizerEquiv_invFun_eq** 是 Mathlib 中的一个引理，位于命名空间 `DomMulAct`。
形式化陈述：stabilizerEquiv_invFun_eq (g : forall i, Perm {a // f a = i}) {a : α} {i :
 ι} (h : f a = i) : stabilizerEquiv_invFun g a = g i ⟨a, h⟩
参数：g : forall i, Perm {a // f a = i}；h : f a = i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stabilizerEquiv_invFun_eq (g : ∀ i, Perm {a // f a = i}) {a : α} {i : ι} (h : f a = i) :
    stabilizerEquiv_invFun g a = g i ⟨a, h⟩ := by subst h; rfl
/-
**DomMulAct.comp_stabilizerEquiv_invFun** 是 Mathlib 中的一个引理，位于命名空间 `DomMulAct`。
形式化陈述：comp_stabilizerEquiv_invFun (g : forall i, Perm {a // f a = i}) (a : α) : 
f (stabilizerEquiv_invFun g a) = f a
参数：g : forall i, Perm {a // f a = i}；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma comp_stabilizerEquiv_invFun (g : ∀ i, Perm {a // f a = i}) (a : α) :
    f (stabilizerEquiv_invFun g a) = f a :=
  (g (f a) ⟨a, rfl⟩).prop

/-- The `invFun` component of `MulEquiv` from `MulAction.stabilizer (Perm α) p`
  to the product of the `Equiv.Perm {a | f a = i}` (as an `Equiv.Perm α`). -/
/-
**DomMulAct.stabilizerEquiv_invFun_aux** 是 Mathlib 中的一个定义，位于命名空间 `DomMulAct`。
形式化陈述：stabilizerEquiv_invFun_aux (g : forall i, Perm {a // f a = i}) : Perm α wh
ere toFun
参数：g : forall i, Perm {a // f a = i}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The `invFun` component of `MulEquiv` from `MulAction.stabilizer (Perm α) p`
  to the product of the `Equiv.Perm {a | f a = i}` (as an `Equiv.Perm α`).
-/
def stabilizerEquiv_invFun_aux (g : ∀ i, Perm {a // f a = i}) : Perm α where
  toFun := stabilizerEquiv_invFun g
  invFun := stabilizerEquiv_invFun (fun i ↦ (g i).symm)
  left_inv a := by
    rw [stabilizerEquiv_invFun_eq _ (comp_stabilizerEquiv_invFun g a)]
    exact congr_arg Subtype.val ((g <| f a).left_inv _)
  right_inv a := by
    rw [stabilizerEquiv_invFun_eq _ (comp_stabilizerEquiv_invFun _ a)]
    exact congr_arg Subtype.val ((g <| f a).right_inv _)

variable (f) in
/-- The `MulEquiv` from the `MulOpposite` of `MulAction.stabilizer (Perm α)ᵈᵐᵃ f`
  to the product of the `Equiv.Perm {a // f a = i}` -/
/-
**DomMulAct.stabilizerMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DomMulAct`。
形式化陈述：stabilizerMulEquiv : (stabilizer (Perm α)ᵈᵐᵃ f)ᵐᵒᵖ ≃* (forall i, Perm {a /
/ f a = i}) where toFun g i
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The `MulEquiv` from the `MulOpposite` of `MulAction.stabilizer (Perm α)ᵈᵐᵃ f`
  to the product of the `Equiv.Perm {a // f a = i}`
-/
def stabilizerMulEquiv : (stabilizer (Perm α)ᵈᵐᵃ f)ᵐᵒᵖ ≃* (∀ i, Perm {a // f a = i}) where
  toFun g i := Perm.subtypePerm (mk.symm g.unop) fun a ↦ by
    rw [← Function.comp_apply (f := f), mem_stabilizer_iff.mp g.unop.prop]
  invFun g := ⟨mk (stabilizerEquiv_invFun_aux g), by
    ext a
    rw [smul_apply, symm_apply_apply, Perm.smul_def]
    apply comp_stabilizerEquiv_invFun⟩
  right_inv g := by ext i a; apply stabilizerEquiv_invFun_eq
  map_mul' _ _ := rfl
/-
**DomMulAct.stabilizerMulEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `DomMulAct`。
形式化陈述：stabilizerMulEquiv_apply (g : (stabilizer (Perm α)ᵈᵐᵃ f)ᵐᵒᵖ) {a : α} {i : 
ι} (h : f a = i) : ((stabilizerMulEquiv f)) g i ⟨a, h⟩ = (mk.symm g.unop : Equiv
.Perm α) a
参数：g : (stabilizer (Perm α)ᵈᵐᵃ f)ᵐᵒᵖ；h : f a = i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stabilizerMulEquiv_apply (g : (stabilizer (Perm α)ᵈᵐᵃ f)ᵐᵒᵖ) {a : α} {i : ι} (h : f a = i) :
    ((stabilizerMulEquiv f)) g i ⟨a, h⟩ = (mk.symm g.unop : Equiv.Perm α) a := rfl

section Fintype

variable [Fintype α]

open Nat

variable (f)

/-- The cardinality of the type of permutations preserving a function -/
/-
**DomMulAct.stabilizer_card** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：stabilizer_card [DecidableEq α] [DecidableEq ι] [Fintype ι] : Fintype.card
 {g : Perm α // f ∘ g = f} = ∏ i, (Fintype.card {a // f a = i})!
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Nat.card_pi`：card_pi {β : α -> Type*} [Fintype α] : Nat.card (forall a, 
β a) = ∏ a, Nat.card (β a)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Fintype.card_perm`：Fintype.card_perm [Fintype α] : Fintype.card (Perm α)
 = (Fintype.card α)!

--- 原说明 ---
The cardinality of the type of permutations preserving a function
-/
theorem stabilizer_card [DecidableEq α] [DecidableEq ι] [Fintype ι] :
    Fintype.card {g : Perm α // f ∘ g = f} = ∏ i, (Fintype.card {a // f a = i})! := by
  -- rewriting via Nat.card because Fintype instance is not found
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (subtypeEquiv mk fun _ ↦ ?_),
    Nat.card_congr MulOpposite.opEquiv,
    Nat.card_congr (DomMulAct.stabilizerMulEquiv f).toEquiv, Nat.card_pi]
  · exact Finset.prod_congr rfl fun i _ ↦ by rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  · rfl

omit [Fintype α] in
/-- The cardinality of the set of permutations preserving a function -/
/-
**DomMulAct.stabilizer_ncard** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：stabilizer_ncard [Finite α] [Fintype ι] : Set.ncard {g : Perm α | f ∘ g = 
f} = ∏ i, (Set.ncard {a | f a = i})!
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `DomMulAct.stabilizer_card`：stabilizer_card [DecidableEq α] [DecidableEq 
ι] [Fintype ι] : Fintype.card {g : Perm α // f ∘ g = f} = ∏ i, (Fintype.card {a 
// f a = i})!

--- 原说明 ---
The cardinality of the set of permutations preserving a function
-/
theorem stabilizer_ncard [Finite α] [Fintype ι] :
    Set.ncard {g : Perm α | f ∘ g = f} = ∏ i, (Set.ncard {a | f a = i})! := by
  classical
  cases nonempty_fintype α
  simp only [← Nat.card_coe_set_eq, Set.coe_ofPred, card_eq_fintype_card]
  exact stabilizer_card f

variable [DecidableEq α] [DecidableEq ι]

/-- The cardinality of the type of permutations preserving a function
  (without the finiteness assumption on target) -/
/-
**DomMulAct.stabilizer_card'** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：stabilizer_card' : Fintype.card {g : Perm α // f ∘ g = f} = ∏ i in Finset.
univ.image f, (Fintype.card ({a // f a = i}))!
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DomMulAct.stabilizer_card`：stabilizer_card [DecidableEq α] [DecidableEq 
ι] [Fintype ι] : Fintype.card {g : Perm α // f ∘ g = f} = ∏ i, (Fintype.card {a 
// f a = i})!
· 使用定理 `Finset.prod_bij`：prod_bij (i : forall a in s, κ) (hi : forall a ha, i a 
ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj 
: for…
· 使用定理 `Finset.coe_mem`：coe_mem {s : Finset α} (x : (s : Set α)) : ↑x in s
· 使用定理 `SetCoe.ext`：SetCoe.ext {s : Set α} {a b : s} : (a : α) = b -> a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.refl_apply`：∀ {α : Sort u} (x : α), (Equiv.refl α) x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b

--- 原说明 ---
The cardinality of the type of permutations preserving a function
  (without the finiteness assumption on target)
-/
theorem stabilizer_card' :
    Fintype.card {g : Perm α // f ∘ g = f} =
      ∏ i ∈ Finset.univ.image f, (Fintype.card ({a // f a = i}))! := by
  set φ : α → Finset.univ.image f :=
    Set.codRestrict f (Finset.univ.image f) (fun a => by simp)
  suffices ∀ g : Perm α, f ∘ g = f ↔ φ ∘ g = φ by
    simp only [this, stabilizer_card]
    apply Finset.prod_bij (fun g _ => g.val)
    · exact fun g _ => Finset.coe_mem g
    · exact fun g _ g' _ => SetCoe.ext
    · simp
    · intro i _
      apply congr_arg
      apply Fintype.card_congr
      apply Equiv.subtypeEquiv (Equiv.refl α)
      intro a
      rw [refl_apply, ← Subtype.coe_inj]
      simp only [φ, Set.val_codRestrict_apply]
  · intro g
    simp only [funext_iff]
    apply forall_congr'
    intro a
    simp only [Function.comp_apply, φ, ← Subtype.coe_inj, Set.val_codRestrict_apply]

end Fintype

end DomMulAct

