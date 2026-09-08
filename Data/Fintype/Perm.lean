/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# `Fintype` instances for `Equiv` and `Perm`

Main declarations:
* `permsOfFinset s`: The finset of permutations of the finset `s`.

-/

@[expose] public section

assert_not_exists MonoidWithZero

open Function

open Nat

universe u v

variable {α β γ : Type*}

open Finset List Equiv Equiv.Perm

variable [DecidableEq α] [DecidableEq β]

/-- Given a list, produce a list of all permutations of its elements. -/
/-
**permsOfList** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{α : Type u_1} → [DecidableEq α] → List α → List (Equiv.Perm α)
参数：Equiv.Perm α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a list, produce a list of all permutations of its elements.
-/
def permsOfList : List α → List (Perm α)
  | [] => [1]
  | a :: l => permsOfList l ++ l.flatMap fun b => (permsOfList l).map fun f => Equiv.swap a b * f
/-
**length_permsOfList** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (l : List α), (permsOfList l).leng
th = l.length.factorial
参数：l : List α；permsOfList l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_permsOfList : ∀ l : List α, length (permsOfList l) = l.length !
  | [] => rfl
  | a :: l => by
    simp [Nat.factorial_succ, permsOfList, length_permsOfList, succ_mul, add_comm]
/-
**mem_permsOfList_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_permsOfList_of_mem {l : List α} {f : Perm α} (h : forall x, f x != x -
> x in l) : f in permsOfList l
参数：h : forall x, f x != x -> x in l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_singleton`：∀ {α : Type u_1} {a b : α}, a ∈ [b] ↔ a = b
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.mem_append_left`：∀ {α : Type u} {a : α} {as : List α} (bs : List α)
, a ∈ as → a ∈ as ++ bs
· 使用定理 `List.mem_of_ne_of_mem`：∀ {α : Type u_1} {a y : α} {l : List α}, a ≠ y → 
a ∈ y :: l → a ∈ l
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.Perm.mul_def`：mul_def (f g : Perm α) : f * g = g.trans f
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.swap_swap`：swap_swap (a b : α) : (swap a b).trans (swap a b) = Equ
iv.refl _
· 使用定理 `Equiv.Perm.one_def`：one_def : (1 : Perm α) = Equiv.refl α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem mem_permsOfList_of_mem {l : List α} {f : Perm α} (h : ∀ x, f x ≠ x → x ∈ l) :
    f ∈ permsOfList l := by
  induction l generalizing f with
  | nil =>
    simp only [not_mem_nil] at h
    exact List.mem_singleton.2 (Equiv.ext fun x => Decidable.byContradiction <| h x)
  | cons a l IH =>
  by_cases hfa : f a = a
  · refine mem_append_left _ (IH fun x hx => mem_of_ne_of_mem ?_ (h x hx))
    rintro rfl
    exact hx hfa
  have hfa' : f (f a) ≠ f a := mt (fun h => f.injective h) hfa
  have : ∀ x : α, (Equiv.swap a (f a) * f) x ≠ x → x ∈ l := by
    simp
    grind
  suffices f ∈ permsOfList l ∨ ∃ b ∈ l, ∃ g ∈ permsOfList l, Equiv.swap a b * g = f by
    simpa only [permsOfList, exists_prop, List.mem_map, mem_append, List.mem_flatMap]
  refine or_iff_not_imp_left.2 fun _hfl => ⟨f a, ?_, Equiv.swap a (f a) * f, IH this, ?_⟩
  · exact mem_of_ne_of_mem hfa (h _ hfa')
  · rw [← mul_assoc, mul_def (Equiv.swap a (f a)) (Equiv.swap a (f a)), Equiv.swap_swap,
      ← Perm.one_def, one_mul]
/-
**mem_of_mem_permsOfList** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_of_mem_permsOfList : forall {l : List α} {f : Perm α}, f in permsOfLis
t l -> {x : α} -> f x != x -> x in l | [], f, h, heq_iff_eq => by have : f = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_of_mem_permsOfList :
    ∀ {l : List α} {f : Perm α}, f ∈ permsOfList l → {x : α} → f x ≠ x → x ∈ l
  | [], f, h, heq_iff_eq => by
    have : f = 1 := by simpa [permsOfList] using h
    rw [this]; simp
  | a :: l, f, h, x =>
    (mem_append.1 h).elim (fun h hx => mem_cons_of_mem _ (mem_of_mem_permsOfList h hx))
      fun h hx =>
      let ⟨y, hy, hy'⟩ := List.mem_flatMap.1 h
      let ⟨g, hg₁, hg₂⟩ := List.mem_map.1 hy'
      if hxa : x = a then by simp [hxa]
      else
        if hxy : x = y then mem_cons_of_mem _ <| by rwa [hxy]
        else mem_cons_of_mem a <| mem_of_mem_permsOfList hg₁ <| by
              rw [eq_inv_mul_iff_mul_eq.2 hg₂, mul_apply, swap_inv, swap_apply_def]
              split_ifs <;> [exact Ne.symm hxy; exact Ne.symm hxa; exact hx]
/-
**mem_permsOfList_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_permsOfList_iff {l : List α} {f : Perm α} : f in permsOfList l ↔ foral
l {x}, f x != x -> x in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_of_mem_permsOfList`：mem_of_mem_permsOfList : forall {l : List α} {f 
: Perm α}, f in permsOfList l -> {x : α} -> f x != x -> x in l | [], f, h, heq_i
ff_eq => by …
· 使用定理 `mem_permsOfList_of_mem`：mem_permsOfList_of_mem {l : List α} {f : Perm α}
 (h : forall x, f x != x -> x in l) : f in permsOfList l
-/
theorem mem_permsOfList_iff {l : List α} {f : Perm α} :
    f ∈ permsOfList l ↔ ∀ {x}, f x ≠ x → x ∈ l :=
  ⟨mem_of_mem_permsOfList, mem_permsOfList_of_mem⟩
/-
**nodup_permsOfList** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nodup_permsOfList : forall {l : List α}, l.Nodup -> (permsOfList l).Nodup 
| [], _ => by simp [permsOfList] | a :: l, hl => by have hl' : l.Nodup
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nodup_permsOfList : ∀ {l : List α}, l.Nodup → (permsOfList l).Nodup
  | [], _ => by simp [permsOfList]
  | a :: l, hl => by
    have hl' : l.Nodup := hl.of_cons
    have hln' : (permsOfList l).Nodup := nodup_permsOfList hl'
    have hmeml : ∀ {f : Perm α}, f ∈ permsOfList l → f a = a := fun {f} hf =>
      not_not.1 (mt (mem_of_mem_permsOfList hf) (nodup_cons.1 hl).1)
    rw [permsOfList, List.nodup_append', List.nodup_flatMap, pairwise_iff_getElem]
    refine ⟨?_, ⟨⟨?_,?_ ⟩, ?_⟩⟩
    · exact hln'
    · exact fun _ _ => hln'.map fun _ _ => mul_left_cancel
    · intro i j hi hj hij x hx₁ hx₂
      let ⟨f, hf⟩ := List.mem_map.1 hx₁
      let ⟨g, hg⟩ := List.mem_map.1 hx₂
      have hix : x a = l[i] := by
        rw [← hf.2, mul_apply, hmeml hf.1, swap_apply_left]
      have hiy : x a = l[j] := by
        rw [← hg.2, mul_apply, hmeml hg.1, swap_apply_left]
      have hieqj : i = j := hl'.getElem_inj_iff.1 (hix.symm.trans hiy)
      exact absurd hieqj (_root_.ne_of_lt hij)
    · intro f hf₁ hf₂
      let ⟨x, hx, hx'⟩ := List.mem_flatMap.1 hf₂
      let ⟨g, hg⟩ := List.mem_map.1 hx'
      obtain rfl : g.symm x = a := f.injective <| by rw [hmeml hf₁, ← hg.2]; simp
      have hxa : x ≠ g.symm x := fun h => (List.nodup_cons.1 hl).1 (h ▸ hx)
      exact (List.nodup_cons.1 hl).1 <| mem_of_mem_permsOfList hg.1 (by simpa using hxa)

set_option backward.isDefEq.respectTransparency false in
/-- Given a finset, produce the finset of all permutations of its elements. -/
/-
**permsOfFinset** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：permsOfFinset (s : Finset α) : Finset (Perm α)
参数：s : Finset α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `nodup_permsOfList`：nodup_permsOfList : forall {l : List α}, l.Nodup -> (
permsOfList l).Nodup | [], _ => by simp [permsOfList] | a :: l, hl => by have hl
' : l.N…
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup

--- 原说明 ---
Given a finset, produce the finset of all permutations of its elements.
-/
def permsOfFinset (s : Finset α) : Finset (Perm α) :=
  Quotient.hrecOn s.1 (fun l hl => ⟨permsOfList l, nodup_permsOfList hl⟩)
    (fun a b hab =>
      hfunext (congr_arg _ (Quotient.sound hab)) fun ha hb _ =>
        heq_of_eq <| Finset.ext <| by simp [mem_permsOfList_iff, hab.mem_iff])
    s.2
/-
**mem_perms_of_finset_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_perms_of_finset_iff : forall {s : Finset α} {f : Perm α}, f in permsOf
Finset s ↔ forall {x}, f x != x -> x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_permsOfList_iff`：mem_permsOfList_iff {l : List α} {f : Perm α} : f i
n permsOfList l ↔ forall {x}, f x != x -> x in l
-/
theorem mem_perms_of_finset_iff :
    ∀ {s : Finset α} {f : Perm α}, f ∈ permsOfFinset s ↔ ∀ {x}, f x ≠ x → x ∈ s := by
  rintro ⟨⟨l⟩, hs⟩ f; exact mem_permsOfList_iff
/-
**card_perms_of_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_perms_of_finset : forall s : Finset α, #(permsOfFinset s) = (#s)!
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `length_permsOfList`：∀ {α : Type u_1} [inst : DecidableEq α] (l : List α)
, (permsOfList l).length = l.length.factorial
-/
theorem card_perms_of_finset : ∀ s : Finset α, #(permsOfFinset s) = (#s)! := by
  rintro ⟨⟨l⟩, hs⟩; exact length_permsOfList l

/-- The collection of permutations of a fintype is a fintype. -/
@[instance_reducible]
/-
**fintypePerm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fintypePerm [Fintype α] : Fintype (Perm α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The collection of permutations of a fintype is a fintype.
-/
def fintypePerm [Fintype α] : Fintype (Perm α) :=
  ⟨permsOfFinset (@Finset.univ α _), by simp [mem_perms_of_finset_iff]⟩
/-
**Equiv.instFintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Equiv.instFintype [Fintype α] [Fintype β] : Fintype (α ≃ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance Equiv.instFintype [Fintype α] [Fintype β] : Fintype (α ≃ β) :=
  if h : Fintype.card β = Fintype.card α then
    Trunc.recOnSubsingleton (Fintype.truncEquivFin α) fun eα =>
      Trunc.recOnSubsingleton (Fintype.truncEquivFin β) fun eβ =>
        @Fintype.ofEquiv _ (Perm α) fintypePerm
          (equivCongr (Equiv.refl α) (eα.trans (Eq.recOn h eβ.symm)) : α ≃ α ≃ (α ≃ β))
  else ⟨∅, fun x => False.elim (h (Fintype.card_eq.2 ⟨x.symm⟩))⟩

@[to_additive]
/-
**MulEquiv.instFintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulEquiv.instFintype {α β : Type*} [Mul α] [Mul β] [DecidableEq α] [Decida
bleEq β] [Fintype α] [Fintype β] : Fintype (α ≃* β) where elems
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MulEquiv.instFintype
    {α β : Type*} [Mul α] [Mul β] [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] :
    Fintype (α ≃* β) where
  elems := Equiv.instFintype.elems.filterMap
    (fun e => if h : ∀ a b : α, e (a * b) = e a * e b then (⟨e, h⟩ : α ≃* β) else none) (by aesop)
  complete me := (Finset.mem_filterMap ..).mpr ⟨me.toEquiv, Finset.mem_univ _, by {simp; rfl}⟩
/-
**Fintype.card_perm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_perm [Fintype α] : Fintype.card (Perm α) = (Fintype.card α)!
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `card_perms_of_finset`：card_perms_of_finset : forall s : Finset α, #(perm
sOfFinset s) = (#s)!
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem Fintype.card_perm [Fintype α] : Fintype.card (Perm α) = (Fintype.card α)! :=
  Subsingleton.elim (@fintypePerm α _ _) (@Equiv.instFintype α α _ _ _ _) ▸ card_perms_of_finset _
/-
**Fintype.card_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_equiv [Fintype α] [Fintype β] (e : α ≃ β) : Fintype.card (α ≃
 β) = (Fintype.card α)!
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_perm`：Fintype.card_perm [Fintype α] : Fintype.card (Perm α)
 = (Fintype.card α)!
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem Fintype.card_equiv [Fintype α] [Fintype β] (e : α ≃ β) :
    Fintype.card (α ≃ β) = (Fintype.card α)! :=
  Fintype.card_congr (equivCongr (Equiv.refl α) e) ▸ Fintype.card_perm
