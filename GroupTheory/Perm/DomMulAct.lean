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

variable {α ι : Type*} {f : α -> ι}

namespace DomMulAct

/--
lemma `mem_stabilizer_iff` / 引理 `mem_stabilizer_iff`

English:
lemma mem_stabilizer_iff
  given: {g : (Perm α)ᵈᵐᵃ}
  proof: by
  simp only [MulAction.mem_stabilizer_iff]; rfl

中文:
引理 mem_stabilizer_iff
  条件: {g : (置换 α)ᵈᵐᵃ}
  证明: by
  simp only [MulAction.mem_stabilizer_iff]; rfl

Depends on / 依赖: MulAction, MulAction.mem_stabilizer_iff, mem_stabilizer_iff
-/
lemma mem_stabilizer_iff {g : (Perm α)ᵈᵐᵃ} :
    g in stabilizer (Perm α)ᵈᵐᵃ f ↔ f ∘ (mk.symm g :) = f := by
  simp only [MulAction.mem_stabilizer_iff]; rfl

/--
Definition of `stabilizerEquiv_invFun` / `stabilizerEquiv_invFun` 的定义

English:
definition stabilizerEquiv_invFun
  signature: (g : forall i, Perm {a // f a = i}) (a : α)
  body: g (f a) ⟨a, rfl⟩

中文:
定义 stabilizerEquiv_invFun
  签名: (g : 对任意 i, 置换 {a // f a = i}) (a : α)
  定义体: g (f a) ⟨a, rfl⟩
-/
def stabilizerEquiv_invFun (g : forall i, Perm {a // f a = i}) (a : α) : α := g (f a) ⟨a, rfl⟩

/--
lemma `stabilizerEquiv_invFun_eq` / 引理 `stabilizerEquiv_invFun_eq`

English:
lemma stabilizerEquiv_invFun_eq
  given: (g : forall i, Perm {a // f a = i}) {a : α} {i : ι} (h : f a = i)
  proof: by subst h; rfl

中文:
引理 stabilizerEquiv_invFun_eq
  条件: (g : 对任意 i, 置换 {a // f a = i}) {a : α} {i : ι} (h : f a = i)
  证明: by subst h; rfl
-/
lemma stabilizerEquiv_invFun_eq (g : forall i, Perm {a // f a = i}) {a : α} {i : ι} (h : f a = i) :
    stabilizerEquiv_invFun g a = g i ⟨a, h⟩ := by subst h; rfl

/--
lemma `comp_stabilizerEquiv_invFun` / 引理 `comp_stabilizerEquiv_invFun`

English:
lemma comp_stabilizerEquiv_invFun
  given: (g : forall i, Perm {a // f a = i}) (a : α)
  proof: (g (f a) ⟨a, rfl⟩).prop

中文:
引理 comp_stabilizerEquiv_invFun
  条件: (g : 对任意 i, 置换 {a // f a = i}) (a : α)
  证明: (g (f a) ⟨a, rfl⟩).prop
-/
lemma comp_stabilizerEquiv_invFun (g : forall i, Perm {a // f a = i}) (a : α) :
    f (stabilizerEquiv_invFun g a) = f a :=
  (g (f a) ⟨a, rfl⟩).prop

/--
Definition of `stabilizerEquiv_invFun_aux` / `stabilizerEquiv_invFun_aux` 的定义

English:
definition stabilizerEquiv_invFun_aux
  signature: (g : forall i, Perm {a // f a = i})
  body: stabilizerEquiv_invFun g
  invFun := stabilizerEquiv_invFun (fun i => (g i).symm)
  left_inv a := by
    rw [stabilizerEquiv_invFun_eq _ (comp_stabilizerEquiv_invFun g a)]
    exact congr_arg Subtype.val ((g <| f a).left_inv _)
  right_inv a := by
    rw [stabilizerEquiv_invFun_eq _ (comp_stabilizerEquiv_invFun _ a)]
    exact congr_arg Subtype.val ((g <| f a).right_inv _)

中文:
定义 stabilizerEquiv_invFun_aux
  签名: (g : 对任意 i, 置换 {a // f a = i})
  定义体: stabilizerEquiv_invFun g
  invFun := stabilizerEquiv_invFun (fun i => (g i).symm)
  left_inv a := by
    rw [stabilizerEquiv_invFun_eq _ (comp_stabilizerEquiv_invFun g a)]
    exact congr_arg Subtype.val ((g <| f a).left_inv _)
  right_inv a := by
    rw [stabilizerEquiv_invFun_eq _ (comp_stabilizerEquiv_invFun _ a)]
    exact congr_arg Subtype.val ((g <| f a).right_inv _)

Depends on / 依赖: stabilizerEquiv_invFun
-/
def stabilizerEquiv_invFun_aux (g : forall i, Perm {a // f a = i}) : Perm α where
  toFun := stabilizerEquiv_invFun g
  invFun := stabilizerEquiv_invFun (fun i => (g i).symm)
  left_inv a := by
    rw [stabilizerEquiv_invFun_eq _ (comp_stabilizerEquiv_invFun g a)]
    exact congr_arg Subtype.val ((g <| f a).left_inv _)
  right_inv a := by
    rw [stabilizerEquiv_invFun_eq _ (comp_stabilizerEquiv_invFun _ a)]
    exact congr_arg Subtype.val ((g <| f a).right_inv _)

variable (f) in
/--
Definition of `stabilizerMulEquiv` / `stabilizerMulEquiv` 的定义

English:
definition stabilizerMulEquiv
  signature: : (stabilizer (Perm α)ᵈᵐᵃ f)ᵐᵒᵖ ≃* (forall i, Perm {a // f a = i}) where
  body: Perm.subtypePerm (mk.symm g.unop) fun a => by
    rw [← Function.comp_apply (f := f)]; rw [mem_stabilizer_iff.mp g.unop.prop]
  invFun g := ⟨mk (stabilizerEquiv_invFun_aux g), by
    ext a
    rw [smul_apply]; rw [symm_apply_apply]; rw [Perm.smul_def]
    apply comp_stabilizerEquiv_invFun⟩
  right_inv g := by ext i a; apply stabilizerEquiv_invFun_eq
  map_mul' _ _ := rfl

中文:
定义 stabilizerMulEquiv
  签名: : (stabilizer (置换 α)ᵈᵐᵃ f)ᵐᵒᵖ ≃* (对任意 i, 置换 {a // f a = i}) where
  定义体: Perm.subtypePerm (mk.symm g.unop) fun a => by
    rw [← Function.comp_apply (f := f)]; rw [mem_stabilizer_iff.mp g.unop.prop]
  invFun g := ⟨mk (stabilizerEquiv_invFun_aux g), by
    ext a
    rw [smul_apply]; rw [symm_apply_apply]; rw [Perm.smul_def]
    apply comp_stabilizerEquiv_invFun⟩
  right_inv g := by ext i a; apply stabilizerEquiv_invFun_eq
  map_mul' _ _ := rfl

Depends on / 依赖: Function, Function.comp_apply, Perm.smul_def, Perm.subtypePerm, comp_apply, comp_stabilizerEquiv_invFun, g.unop, g.unop.prop, invFun, map_mul, mem_stabilizer_iff, mem_stabilizer_iff.mp, mk.symm, right_inv, smul_apply, smul_def, stabilizerEquiv_invFun_aux, stabilizerEquiv_invFun_eq, subtypePerm, symm_apply_apply
-/
def stabilizerMulEquiv : (stabilizer (Perm α)ᵈᵐᵃ f)ᵐᵒᵖ ≃* (forall i, Perm {a // f a = i}) where
  toFun g i := Perm.subtypePerm (mk.symm g.unop) fun a => by
    rw [← Function.comp_apply (f := f)]; rw [mem_stabilizer_iff.mp g.unop.prop]
  invFun g := ⟨mk (stabilizerEquiv_invFun_aux g), by
    ext a
    rw [smul_apply]; rw [symm_apply_apply]; rw [Perm.smul_def]
    apply comp_stabilizerEquiv_invFun⟩
  right_inv g := by ext i a; apply stabilizerEquiv_invFun_eq
  map_mul' _ _ := rfl

/--
lemma `stabilizerMulEquiv_apply` / 引理 `stabilizerMulEquiv_apply`

English:
lemma stabilizerMulEquiv_apply
  given: (g : (stabilizer (Perm α)ᵈᵐᵃ f)ᵐᵒᵖ) {a : α} {i : ι} (h : f a = i)
  proof: rfl

中文:
引理 stabilizerMulEquiv_apply
  条件: (g : (stabilizer (置换 α)ᵈᵐᵃ f)ᵐᵒᵖ) {a : α} {i : ι} (h : f a = i)
  证明: rfl
-/
lemma stabilizerMulEquiv_apply (g : (stabilizer (Perm α)ᵈᵐᵃ f)ᵐᵒᵖ) {a : α} {i : ι} (h : f a = i) :
    ((stabilizerMulEquiv f)) g i ⟨a, h⟩ = (mk.symm g.unop : Equiv.Perm α) a := rfl

section Fintype

variable [Fintype α]

open Nat

variable (f)

/--
theorem `stabilizer_card` / 定理 `stabilizer_card`

English:
theorem stabilizer_card
  given: [DecidableEq α] [DecidableEq ι] [Fintype ι]
  proof: by
  -- rewriting via Nat.card because Fintype instance is not found
  rw [← Nat.card_eq_fintype_card]; rw [Nat.card_congr (subtypeEquiv mk fun _ => ?_)]; rw [Nat.card_congr MulOpposite.opEquiv]; rw [Nat.card_congr (DomMulAct.stabilizerMulEquiv f).toEquiv]; rw [Nat.card_pi]
  · exact Finset.prod_congr rfl fun i _ => by rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  · rfl

omit [Fintype α] in

中文:
定理 stabilizer_card
  条件: [DecidableEq α] [DecidableEq ι] [有限类型 ι]
  证明: by
  -- rewriting via Nat.card because Fintype instance is not found
  rw [← Nat.card_eq_fintype_card]; rw [Nat.card_congr (subtypeEquiv mk fun _ => ?_)]; rw [Nat.card_congr MulOpposite.opEquiv]; rw [Nat.card_congr (DomMulAct.stabilizerMulEquiv f).toEquiv]; rw [Nat.card_pi]
  · exact Finset.prod_congr rfl fun i _ => by rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  · rfl

omit [Fintype α] in
-/
theorem stabilizer_card [DecidableEq α] [DecidableEq ι] [Fintype ι] :
    Fintype.card {g : Perm α // f ∘ g = f} = ∏ i, (Fintype.card {a // f a = i})! := by
  -- rewriting via Nat.card because Fintype instance is not found
  rw [← Nat.card_eq_fintype_card]; rw [Nat.card_congr (subtypeEquiv mk fun _ => ?_)]; rw [Nat.card_congr MulOpposite.opEquiv]; rw [Nat.card_congr (DomMulAct.stabilizerMulEquiv f).toEquiv]; rw [Nat.card_pi]
  · exact Finset.prod_congr rfl fun i _ => by rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  · rfl

omit [Fintype α] in
/--
theorem `stabilizer_ncard` / 定理 `stabilizer_ncard`

English:
theorem stabilizer_ncard
  given: [Finite α] [Fintype ι]
  proof: by
  classical
  cases nonempty_fintype α
  simp only [← Nat.card_coe_set_eq, Set.coe_ofPred, card_eq_fintype_card]
  exact stabilizer_card f

中文:
定理 stabilizer_ncard
  条件: [有限 α] [有限类型 ι]
  证明: by
  classical
  cases nonempty_fintype α
  simp only [← Nat.card_coe_set_eq, Set.coe_ofPred, card_eq_fintype_card]
  exact stabilizer_card f

Depends on / 依赖: Nat.card_coe_set_eq, Set.coe_ofPred, card_coe_set_eq, card_eq_fintype_card, classical, coe_ofPred, nonempty_fintype, stabilizer_card
-/
theorem stabilizer_ncard [Finite α] [Fintype ι] :
    Set.ncard {g : Perm α | f ∘ g = f} = ∏ i, (Set.ncard {a | f a = i})! := by
  classical
  cases nonempty_fintype α
  simp only [← Nat.card_coe_set_eq, Set.coe_ofPred, card_eq_fintype_card]
  exact stabilizer_card f

variable [DecidableEq α] [DecidableEq ι]

/--
theorem `stabilizer_card'` / 定理 `stabilizer_card'`

English:
theorem stabilizer_card'
  proof: by
  set φ : α -> Finset.univ.image f :=
    Set.codRestrict f (Finset.univ.image f) (fun a => by simp)
  suffices forall g : Perm α, f ∘ g = f ↔ φ ∘ g = φ by
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
      rw [refl_apply]; rw [← Subtype.coe_inj]
      simp only [φ, Set.val_codRestrict_apply]
  · intro g
    simp only [funext_iff]
    apply forall_congr'
    intro a
    simp only [Function.comp_apply, φ, ← Subtype.coe_inj, Set.val_codRestrict_apply]

中文:
定理 stabilizer_card'
  证明: by
  set φ : α -> Finset.univ.image f :=
    Set.codRestrict f (Finset.univ.image f) (fun a => by simp)
  suffices forall g : Perm α, f ∘ g = f ↔ φ ∘ g = φ by
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
      rw [refl_apply]; rw [← Subtype.coe_inj]
      simp only [φ, Set.val_codRestrict_apply]
  · intro g
    simp only [funext_iff]
    apply forall_congr'
    intro a
    simp only [Function.comp_apply, φ, ← Subtype.coe_inj, Set.val_codRestrict_apply]

Depends on / 依赖: Equiv.refl, Equiv.subtypeEquiv, Finset, Finset.coe_mem, Finset.prod_bij, Finset.univ.image, Fintype, Fintype.card_congr, Set.codRestrict, Set.val_codRestrict_apply, SetCoe, SetCoe.ext, Subtype, Subtype.coe_inj, card_congr, codRestrict, coe_inj, coe_mem, congr_arg, g.val
-/
theorem stabilizer_card' :
    Fintype.card {g : Perm α // f ∘ g = f} =
      ∏ i in Finset.univ.image f, (Fintype.card ({a // f a = i}))! := by
  set φ : α -> Finset.univ.image f :=
    Set.codRestrict f (Finset.univ.image f) (fun a => by simp)
  suffices forall g : Perm α, f ∘ g = f ↔ φ ∘ g = φ by
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
      rw [refl_apply]; rw [← Subtype.coe_inj]
      simp only [φ, Set.val_codRestrict_apply]
  · intro g
    simp only [funext_iff]
    apply forall_congr'
    intro a
    simp only [Function.comp_apply, φ, ← Subtype.coe_inj, Set.val_codRestrict_apply]

end Fintype

end DomMulAct
