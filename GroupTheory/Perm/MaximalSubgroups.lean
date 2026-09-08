/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.GroupAction.Jordan
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

/-! # Maximal subgroups of the symmetric groups

* `Equiv.Perm.isCoatom_stabilizer`:
  if neither `s : Set α` nor its complementary subset is empty,
  and the cardinality of `s` is not half of that of `α`,
  then `MulAction.stabilizer (Equiv.Perm α) s` is
  a maximal subgroup of the symmetric group `Equiv.Perm α`.

  This is the *intransitive case* of the O'Nan-Scott classification.

## TODO

  * Application to primitivity of the action
    of `Equiv.Perm α` on finite combinations of `α`.

  * Formalize the other cases of the classification.
    The next one should be the *imprimitive case*.

## Reference

The argument is taken from [M. Liebeck, C. Praeger, J. Saxl,
*A classification of the maximal subgroups of the finite
alternating and symmetric groups*, 1987][LiebeckPraegerSaxl-1987].
-/

public section

open scoped Pointwise

open Set

variable {M α : Type*} [Group M] [MulAction M α] {s : Set α}

namespace MulAction

open Equiv

variable (s) in
/- Note : Under the hypothesis, multiple transitivity would also hold. -/
/-- In the permutation group, the stabilizer of any set
acts primitively on that set. -/
/-
**MulAction.isPreprimitive_stabilizer_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `M
ulAction`。
形式化陈述：isPreprimitive_stabilizer_of_surjective (hs : Function.Surjective (toPerm 
: stabilizer M s -> Perm s)) : IsPreprimitive (stabilizer M s) s
参数：hs : Function.Surjective (toPerm : stabilizer M s -> Perm s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.isPreprimitive_congr`：isPreprimitive_congr (hφ : Function.Surj
ective φ) (hf : Function.Bijective f) : IsPreprimitive M α ↔ IsPreprimitive N β
· 使用定理 `Equiv.Perm.instIsPreprimitive`：∀ {α : Type u_1}, MulAction.IsPreprimitiv
e (Equiv.Perm α) α

--- 原说明 ---
In the permutation group, the stabilizer of any set
acts primitively on that set.
-/
theorem isPreprimitive_stabilizer_of_surjective
    (hs : Function.Surjective (toPerm : stabilizer M s → Perm s)) :
    IsPreprimitive (stabilizer M s) s := by
  let φ : stabilizer M s → Perm s := toPerm
  let f : s →ₑ[φ] s := {
    toFun := id
    map_smul' _ _ := rfl }
  have hf : Function.Bijective f := Function.bijective_id
  rw [isPreprimitive_congr hs hf]
  infer_instance

/-- A (mostly trivial) primitivity criterion for stabilizers. -/
/-
**MulAction.isPreprimitive_stabilizer_subgroup** 是 Mathlib 中的一个定理，位于命名空间 `MulAct
ion`。
形式化陈述：isPreprimitive_stabilizer_subgroup [IsPreprimitive (stabilizer M s) s] {G 
: Subgroup M} (hG : stabilizer M s <= G) : IsPreprimitive (stabilizer G s) s
参数：stabilizer M s；hG : stabilizer M s <= G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `MulAction.IsPreprimitive.of_surjective`：∀ {M : Type u_3} [inst : Group M
] {α : Type u_4} [inst_1 : MulAction M α] {N : Type u_5} {β : Type u_6}   [inst_
2 : Group N] [inst_3 : MulAc…
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id

--- 原说明 ---
A (mostly trivial) primitivity criterion for stabilizers.
-/
theorem isPreprimitive_stabilizer_subgroup [IsPreprimitive (stabilizer M s) s]
    {G : Subgroup M} (hG : stabilizer M s ≤ G) :
    IsPreprimitive (stabilizer G s) s :=
  let φ (g : stabilizer M s) : stabilizer G s :=
    ⟨⟨g, hG g.prop⟩, g.prop⟩
  let f : s →ₑ[φ] s := {
      toFun := id
      map_smul' _ _ := rfl }
  IsPreprimitive.of_surjective (f := f) Function.surjective_id
/-
**MulAction.IsPretransitive.of_partition** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.Is
Pretransitive`。
形式化陈述：∀ {M : Type u_1} {α : Type u_2} [inst : Group M] [inst_1 : MulAction M α] 
{s : Set α},   (∀ a ∈ s, ∀ b ∈ s, ∃ g, g • a = b) →     (∀ a ∈ sᶜ, ∀ b ∈ sᶜ, ∃ g
, g • a = b) → MulAction.stabilizer M s ≠ ⊤ → MulAction.IsPretransitive M α
参数：∀ a ∈ s, ∀ b ∈ s, ∃ g, g • a = b；∀ a ∈ sᶜ, ∀ b ∈ sᶜ, ∃ g, g • a = b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `MulAction.le_stabilizer_iff_smul_le`：le_stabilizer_iff_smul_le (s : Set 
α) (H : Subgroup G) : H <= stabilizer G s ↔ forall g in H, g • s subseteq s
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.mem_compl`：mem_compl {s : Set α} {x : α} (h : x ∉ s) : x in sᶜ
· 使用定理 `MulAction.isPretransitive_iff_base`：isPretransitive_iff_base (a : X) : I
sPretransitive G X ↔ forall x : X, exists g : G, g • a = x where mp hG x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem IsPretransitive.of_partition
    (hs : ∀ a ∈ s, ∀ b ∈ s, ∃ g : M, g • a = b)
    (hs' : ∀ a ∈ sᶜ, ∀ b ∈ sᶜ, ∃ g : M, g • a = b)
    (hM : stabilizer M s ≠ ⊤) :
    IsPretransitive M α := by
  suffices ∃ (a b : α) (g : M), a ∈ s ∧ b ∈ sᶜ ∧ g • a = b by
    obtain ⟨a, b, g, ha, hb, hgab⟩ := this
    rw [isPretransitive_iff_base a]
    intro x
    by_cases hx : x ∈ s
    · exact hs a ha x hx
    · rw [← Set.mem_compl_iff] at hx
      obtain ⟨k, hk⟩ := hs' b hb x hx
      use k * g
      rw [mul_smul, hgab, hk]
  contrapose! hM
  rw [eq_top_iff, le_stabilizer_iff_smul_le]
  rintro g _ b ⟨a, ha, hgab⟩
  by_contra hb
  exact hM a b g ha (Set.mem_compl hb) hgab

end MulAction

namespace Equiv.Perm

open MulAction

/-
**Equiv.Perm.ofSubtype_mem_stabilizer** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：ofSubtype_mem_stabilizer [DecidablePred fun x => x in s] (g : Perm s) : g.
ofSubtype in stabilizer (Perm α) s
参数：g : Perm s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_mem`：ofSubtype_apply_of_mem (f : Perm (Sub
type p)) (ha : p a) : ofSubtype f a = f ⟨a, ha⟩
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.Perm.ofSubtype_apply_coe`：ofSubtype_apply_coe (f : Perm (Subtype p
)) (x : Subtype p) : ofSubtype f x = f x
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem ofSubtype_mem_stabilizer [DecidablePred fun x ↦ x ∈ s] (g : Perm s) :
    g.ofSubtype ∈ stabilizer (Perm α) s := by
  rw [mem_stabilizer_iff]
  ext g'
  simp_rw [mem_smul_set, Perm.smul_def]
  refine ⟨?_, fun a ↦ ?_⟩
  · rintro ⟨w, hs, rfl⟩
    simp [ofSubtype_apply_of_mem _ hs]
  · use (g⁻¹ ⟨g', a⟩)
    simp
/-
**Equiv.Perm.swap_mem_stabilizer** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：swap_mem_stabilizer [DecidableEq α] {a b : α} {s : Set α} (ha : a in s) (h
b : b in s) : swap a b in stabilizer (Perm α) s
参数：ha : a in s；hb : b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.subset_smul_set_iff`：subset_smul_set_iff : A subseteq a • B ↔ a⁻¹ • 
A subseteq B
-/
theorem swap_mem_stabilizer [DecidableEq α]
    {a b : α} {s : Set α} (ha : a ∈ s) (hb : b ∈ s) :
    swap a b ∈ stabilizer (Perm α) s := by
  suffices swap a b • s ⊆ s by
    rw [mem_stabilizer_iff]
    apply Set.Subset.antisymm this
    exact Set.subset_smul_set_iff.mpr this
  rintro _ ⟨x, hx, rfl⟩
  by_cases h : x ∈ ({a, b} : Set α)
  · aesop
  · have := swap_apply_of_ne_of_ne (a := a) (b := b) (x := x)
    aesop
/-
**Equiv.Perm.exists_mem_stabilizer_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
`。
形式化陈述：exists_mem_stabilizer_smul_eq : forall a in s, forall b in s, exists g in 
stabilizer (Perm α) s, g • a = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.swap_mem_stabilizer`：swap_mem_stabilizer [DecidableEq α] {a b
 : α} {s : Set α} (ha : a in s) (hb : b in s) : swap a b in stabilizer (Perm α) 
s
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
-/
theorem exists_mem_stabilizer_smul_eq :
    ∀ a ∈ s, ∀ b ∈ s, ∃ g ∈ stabilizer (Perm α) s, g • a = b := by
  intro a ha b hb
  classical
  exact ⟨swap a b, swap_mem_stabilizer ha hb, swap_apply_left a b⟩
/-
**Equiv.Perm.stabilizer.surjective_toPerm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.
stabilizer`。
形式化陈述：∀ {α : Type u_2} (s : Set α), Function.Surjective MulAction.toPerm
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ofSubtype_mem_stabilizer`：ofSubtype_mem_stabilizer [Decidable
Pred fun x => x in s] (g : Perm s) : g.ofSubtype in stabilizer (Perm α) s
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.toPerm_apply`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α]
 [inst_1 : MulAction α β] (a : α) (x : β),   (MulAction.toPerm a) x = a • x
· 使用定理 `Equiv.Perm.ofSubtype_apply_coe`：ofSubtype_apply_coe (f : Perm (Subtype p
)) (x : Subtype p) : ofSubtype f x = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stabilizer.surjective_toPerm (s : Set α) :
    Function.Surjective (toPerm : stabilizer (Perm α) s → Perm s) := fun g ↦ by
  classical
  use! Perm.ofSubtype g
  · apply ofSubtype_mem_stabilizer
  · aesop

/-- In the permutation group, the stabilizer of a set acts primitively on that set. -/
/-
**Equiv.Perm.stabilizer_isPreprimitive** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm`。
形式化陈述：stabilizer_isPreprimitive (s : Set α) : IsPreprimitive (stabilizer (Perm α
) s) s
参数：s : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.isPreprimitive_stabilizer_of_surjective`：isPreprimitive_stabil
izer_of_surjective (hs : Function.Surjective (toPerm : stabilizer M s -> Perm s)
) : IsPreprimitive (stabilizer M s) s
· 使用定理 `Equiv.Perm.stabilizer.surjective_toPerm`：∀ {α : Type u_2} (s : Set α), F
unction.Surjective MulAction.toPerm

--- 原说明 ---
In the permutation group, the stabilizer of a set acts primitively on that set.
-/
instance stabilizer_isPreprimitive (s : Set α) :
    IsPreprimitive (stabilizer (Perm α) s) s :=
  isPreprimitive_stabilizer_of_surjective s (stabilizer.surjective_toPerm s)
/-
**Equiv.Perm.stabilizer_ne_top_of_nonempty_of_nonempty_compl** 是 Mathlib 中的一个定理，
位于命名空间 `Equiv.Perm`。
形式化陈述：stabilizer_ne_top_of_nonempty_of_nonempty_compl {s : Set α} (hs : s.Nonemp
ty) (hsc : sᶜ.Nonempty) : stabilizer (Perm α) s != ⊤
参数：hs : s.Nonempty；hsc : sᶜ.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用定理 `Set.mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t :
 Set β} {a : α} {x : β}, x ∈ a • t ↔ ∃ y ∈ t, a • y = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem stabilizer_ne_top_of_nonempty_of_nonempty_compl
    {s : Set α} (hs : s.Nonempty) (hsc : sᶜ.Nonempty) :
    stabilizer (Perm α) s ≠ ⊤ := by
  classical
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := hsc
  intro h
  rw [Set.mem_compl_iff] at hb; apply hb
  have hg : swap a b ∈ stabilizer (Perm α) s := by simp_all
  rw [mem_stabilizer_iff] at hg
  rw [← hg, Set.mem_smul_set]
  aesop
/-
**Equiv.Perm.has_swap_mem_of_lt_stabilizer** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
`。
形式化陈述：has_swap_mem_of_lt_stabilizer [DecidableEq α] (s : Set α) (G : Subgroup (P
erm α)) (hG : stabilizer (Perm α) s < G) : exists g : Perm α, g.IsSwap ∧ g in G
参数：s : Set α；G : Subgroup (Perm α)；hG : stabilizer (Perm α) s < G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.one_lt_encard_iff`：one_lt_encard_iff : 1 < s.encard ↔ exists a b, a 
in s ∧ b in s ∧ a != b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.swap_isSwap_iff`：swap_isSwap_iff {a b : α} : (swap a b).IsSwa
p ↔ a != b
· 使用定理 `Equiv.Perm.swap_mem_stabilizer`：swap_mem_stabilizer [DecidableEq α] {a b
 : α} {s : Set α} (ha : a in s) (hb : b in s) : swap a b in stabilizer (Perm α) 
s
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `stabilizer_compl`：stabilizer_compl {s : Set α} : stabilizer G sᶜ = stabi
lizer G s
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_add_encard_compl`：encard_add_encard_compl (s : Set α) : s.enc
ard + sᶜ.encard = (univ : Set α).encard
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Set.one_le_encard_iff_nonempty`：∀ {α : Type u_1} {s : Set α}, 1 ≤ s.enca
rd ↔ s.Nonempty
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MulAction.stabilizer_empty`：stabilizer_empty : stabilizer G (∅ : Set α) 
= ⊤
· 使用引理 `MulAction.stabilizer_univ`：stabilizer_univ : stabilizer G (Set.univ : Se
t α) = ⊤
· 使用定理 `finite_iff_nonempty_fintype`：finite_iff_nonempty_fintype (α : Type*) : F
inite α ↔ Nonempty (Fintype α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_finite_iff_nonempty_fintype`：univ_finite_iff_nonempty_fintype :
 (univ : Set α).Finite ↔ Nonempty (Fintype α)
· 使用定理 `Set.finite_of_encard_eq_coe`：finite_of_encard_eq_coe {k : Nat} (h : s.en
card = k) : s.Finite
（共 48 条，此处仅展示前 30 条）
-/
theorem has_swap_mem_of_lt_stabilizer [DecidableEq α]
    (s : Set α) (G : Subgroup (Perm α))
    (hG : stabilizer (Perm α) s < G) :
    ∃ g : Perm α, g.IsSwap ∧ g ∈ G := by
  have : ∀ (t : Set α) (_ : 1 < t.encard), ∃ (g : Perm α),
      g.IsSwap ∧ g ∈ stabilizer (Perm α) t := by
    intro t ht
    rw [Set.one_lt_encard_iff] at ht
    obtain ⟨a, b, ha, hb, h⟩ := ht
    use swap a b, Perm.swap_isSwap_iff.mpr h, swap_mem_stabilizer ha hb
  rcases lt_or_ge 1 s.encard with h1 | h1'
  · obtain ⟨g, hg, hg'⟩ := this s h1
    exact ⟨g, hg, hG.le hg'⟩
  rcases lt_or_ge 1 sᶜ.encard with h1c | h1c'
  · obtain ⟨g, hg, hg'⟩ := this sᶜ h1c
    use g, hg
    rw [stabilizer_compl] at hg'
    exact hG.le hg'
  have hα : Set.encard (_root_.Set.univ : Set α) = 2 := by
    rw [← Set.encard_add_encard_compl s]
    have : (1 + 1 : ENat) = 2 := by norm_num
    convert! this <;>
    · apply le_antisymm
      · assumption
      rw [one_le_encard_iff_nonempty, Set.nonempty_iff_ne_empty]
      aesop
  have _ : Finite α := by
    rw [finite_iff_nonempty_fintype]
    refine univ_finite_iff_nonempty_fintype.mp ?_
    exact finite_of_encard_eq_coe hα
  have hα : Nat.card α = 2 := by
    rw [← ENat.card_coe_set_eq, ENat.card_eq_coe_natCard, Nat.card_coe_set_eq, ncard_univ] at hα
    exact ENat.natCast_inj.mp hα
  have hα2 : Fact (Nat.card (Perm α)).Prime := by
    apply Fact.mk
    rw [Nat.card_perm, hα, Nat.factorial_two]
    exact Nat.prime_two
  cases G.eq_bot_or_eq_top_of_prime_card with
  | inl h =>
    exfalso; exact ne_bot_of_gt hG h
  | inr h =>
    rw [h, ← stabilizer_univ_eq_top (Perm α) α]
    apply this
    simp_all
/-
**Equiv.Perm._root_.Subgroup.isPretransitive_of_stabilizer_lt** 是 Mathlib 中的一个引理
，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Subgroup.isPretransitive_of_stabilizer_lt
    {G : Subgroup M} (hG : stabilizer M s < G)
    (moves : ∀ {s : Set α}, ∀ a ∈ s, ∀ b ∈ s, ∃ g ∈ stabilizer M s, g • a = b) :
    IsPretransitive G α := by
  apply IsPretransitive.of_partition (s := s)
  · intro a ha b hb
    obtain ⟨g, hg, rfl⟩ := moves a ha b hb
    exact ⟨⟨g, hG.le hg⟩, rfl⟩
  · intro a ha b hb
    obtain ⟨g, hg, rfl⟩ := moves a ha b hb
    rw [stabilizer_compl] at hg
    exact ⟨⟨g, hG.le hg⟩, rfl⟩
  · contrapose hG
    apply not_lt_of_ge
    --  `G ≤ stabilizer (Equiv.Perm α) s`
    have : G = Subgroup.map G.subtype ⊤ := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [this, Subgroup.map_le_iff_le_comap]
    rw [show Subgroup.comap G.subtype (stabilizer M s) = stabilizer G s from rfl, hG]

end Equiv.Perm

namespace MulAction.IsBlock

open Equiv Equiv.Perm MulAction SubMulAction

/-
**MulAction.IsBlock.subsingleton_of_ssubset_of_stabilizer_le** 是 Mathlib 中的一个引理，
位于命名空间 `MulAction.IsBlock`。
形式化陈述：subsingleton_of_ssubset_of_stabilizer_le {B : Set α} (hB_ss_sc : B ⊂ s) (h
B : IsBlock M B) (hG : Function.Surjective (MulAction.toPerm : stabilizer M (s :
 Set α) -> Perm (s : Set α))) : B.Subsingleton
参数：hB_ss_sc : B ⊂ s；hB : IsBlock M B；hG : Function.Surjective (MulAction.toPerm 
: stabilizer M (s : Set α) -> Perm (s : Set α))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `subset_of_ssubset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : 
Preorder α] {a b : α}, a ⊂ b → a ⊆ b
· 使用定理 `Subtype.image_preimage_val`：image_preimage_val (s t : Set α) : (Subtype.
val : s -> α) '' Subtype.val ⁻¹' t = s inter t
· 使用定理 `Set.Subsingleton.image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.S
ubsingleton → ∀ (f : α → β), (f '' s).Subsingleton
· 使用定理 `MulAction.isPreprimitive_stabilizer_of_surjective`：isPreprimitive_stabil
izer_of_surjective (hs : Function.Surjective (toPerm : stabilizer M s -> Perm s)
) : IsPreprimitive (stabilizer M s) s
· 使用定理 `MulAction.IsPreprimitive.isTrivialBlock_of_isBlock`：∀ {G : Type u_1} {X 
: Type u_2} {inst : SMul G X} [self : MulAction.IsPreprimitive G X] {B : Set X},
   MulAction.IsBlock G B → MulAction.IsT…
· 使用定理 `MulAction.IsBlock.preimage`：∀ {G : Type u_1} [inst : Group G] {X : Type 
u_2} [inst_1 : MulAction G X] {B : Set X} {H : Type u_3} {Y : Type u_4}   [inst_
2 : Group H] [in…
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Set.preimage_eq_univ_iff`：preimage_eq_univ_iff {f : α -> β} {s} : f ⁻¹' 
s = univ ↔ range f subseteq s
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `not_subset_of_ssubset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [ins
t : Preorder α] {a b : α}, a ⊂ b → ¬b ⊆ a
-/
lemma subsingleton_of_ssubset_of_stabilizer_le
    {B : Set α} (hB_ss_sc : B ⊂ s) (hB : IsBlock M B)
    (hG : Function.Surjective
      (MulAction.toPerm : stabilizer M (s : Set α) → Perm (s : Set α))) :
    B.Subsingleton := by
  rw [← inter_eq_self_of_subset_right (subset_of_ssubset hB_ss_sc), ← Subtype.image_preimage_val]
  apply Set.Subsingleton.image
  suffices IsTrivialBlock (Subtype.val ⁻¹' B : Set (s : Set α)) by
    apply Or.resolve_right this
    rw [preimage_eq_univ_iff, Subtype.range_coe_subtype]
    exact not_subset_of_ssubset hB_ss_sc
  suffices IsPreprimitive (stabilizer M (s : Set α)) (s : Set α) by
    apply this.isTrivialBlock_of_isBlock
    let φ' : stabilizer M (s : Set α) → M := Subtype.val
    let f' : (s : Set α) →ₑ[φ'] α := {
      toFun := Subtype.val
      map_smul' _ _ := rfl }
    exact hB.preimage f'
  exact isPreprimitive_stabilizer_of_surjective _ hG
/-
**MulAction.IsBlock.subsingleton_of_ssubset_of_stabilizer_Perm_le** 是 Mathlib 中的
一个引理，位于命名空间 `MulAction.IsBlock`。
形式化陈述：subsingleton_of_ssubset_of_stabilizer_Perm_le {B : Set α} {G : Subgroup (P
erm α)} (hB : IsBlock G B) (hB_ss_sc : B ⊂ s) (hG : stabilizer (Perm α) s <= G) 
: B.Subsingleton
参数：Perm α；hB : IsBlock G B；hB_ss_sc : B ⊂ s；hG : stabilizer (Perm α) s <= G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.IsBlock.subsingleton_of_ssubset_of_stabilizer_le`：subsingleton
_of_ssubset_of_stabilizer_le {B : Set α} (hB_ss_sc : B ⊂ s) (hB : IsBlock M B) (
hG : Function.Surjective (MulAction.toPerm : sta…
· 使用定理 `Equiv.Perm.stabilizer.surjective_toPerm`：∀ {α : Type u_2} (s : Set α), F
unction.Surjective MulAction.toPerm
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma subsingleton_of_ssubset_of_stabilizer_Perm_le
    {B : Set α} {G : Subgroup (Perm α)} (hB : IsBlock G B)
    (hB_ss_sc : B ⊂ s) (hG : stabilizer (Perm α) s ≤ G) :
    B.Subsingleton := by
  apply hB.subsingleton_of_ssubset_of_stabilizer_le hB_ss_sc
  intro g
  obtain ⟨⟨k, hk⟩, rfl⟩ := stabilizer.surjective_toPerm s g
  let h : G := ⟨k, hG hk⟩
  have : h ∈ stabilizer G s := by aesop
  exact ⟨⟨h, this⟩, rfl⟩
/-
**MulAction.IsBlock.subsingleton_of_stabilizer_lt_of_subset** 是 Mathlib 中的一个引理，位
于命名空间 `MulAction.IsBlock`。
形式化陈述：subsingleton_of_stabilizer_lt_of_subset {B : Set α} {G : Subgroup M} [IsPr
eprimitive (stabilizer G s) s] (hB : IsBlock G B) (hB_not_le_sc : forall (B : Se
t α), IsBlock G B -> B subseteq sᶜ -> B.Subsingleton) (hG : stabilizer M s < G) 
(hBs : B subseteq s) : B.Subsingleton
参数：stabilizer G s；hB : IsBlock G B；hB_not_le_sc : forall (B : Set α), IsBlock G 
B -> B subseteq sᶜ -> B.Subsingleton；hG : stabilizer M s < G；hBs : B subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsPreprimitive.isTrivialBlock_of_isBlock`：∀ {G : Type u_1} {X 
: Type u_2} {inst : SMul G X} [self : MulAction.IsPreprimitive G X] {B : Set X},
   MulAction.IsBlock G B → MulAction.IsT…
· 使用定理 `MulAction.IsBlock.preimage`：∀ {G : Type u_1} [inst : Group G] {X : Type 
u_2} [inst_1 : MulAction G X] {B : Set X} {H : Type u_3} {Y : Type u_4}   [inst_
2 : Group H] [in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Subtype.image_preimage_val`：image_preimage_val (s t : Set α) : (Subtype.
val : s -> α) '' Subtype.val ⁻¹' t = s inter t
· 使用定理 `Set.Subsingleton.image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.S
ubsingleton → ∀ (f : α → β), (f '' s).Subsingleton
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `SetLike.exists_of_lt`：exists_of_lt : p < q -> exists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MulAction.isBlock_iff_smul_eq_or_disjoint`：isBlock_iff_smul_eq_or_disjoi
nt : IsBlock G B ↔ forall g : G, g • B = B ∨ Disjoint (g • B) B
· 使用定理 `MulAction.IsBlock.translate`：∀ {G : Type u_1} [inst : Group G] {X : Type
 u_2} [inst_1 : MulAction G X] {B : Set X} (g : G),   MulAction.IsBlock G B → Mu
lAction.IsBlock G…
· 使用定理 `Disjoint.subset_compl_right`：∀ {α : Type u_1} {s t : Set α}, Disjoint s 
t → s ⊆ tᶜ
· 使用定理 `Set.subsingleton_of_image`：subsingleton_of_image (hf : Function.Injectiv
e f) (s : Set α) (hs : (f '' s).Subsingleton) : s.Subsingleton
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
lemma subsingleton_of_stabilizer_lt_of_subset {B : Set α}
    {G : Subgroup M} [IsPreprimitive (stabilizer G s) s]
    (hB : IsBlock G B)
    (hB_not_le_sc : ∀ (B : Set α), IsBlock G B → B ⊆ sᶜ → B.Subsingleton)
    (hG : stabilizer M s < G) (hBs : B ⊆ s) :
    B.Subsingleton := by
  suffices IsTrivialBlock (Subtype.val ⁻¹' B : Set s) by
    rcases this with hB' | hB'
    · -- trivial case
      rw [← inter_eq_self_of_subset_right hBs, ← Subtype.image_preimage_val]
      apply Set.Subsingleton.image hB'
    · -- `Subtype.val ⁻¹' B = s`
      have hBs' : B = s := Set.Subset.antisymm hBs (by simp_all)
      subst hBs'
      obtain ⟨g', hg', hg's⟩ := SetLike.exists_of_lt hG
      have h := (isBlock_iff_smul_eq_or_disjoint.mp hB ⟨g', hg'⟩).resolve_left hg's
      suffices (g' • B).Subsingleton by
        exact subsingleton_of_image (MulAction.injective g') B this
      apply hB_not_le_sc (⟨g', hg'⟩ • B) (hB.translate _)
      exact Disjoint.subset_compl_right h
  -- `IsTrivialBlock (Subtype.val ⁻¹' B : Set s)`
  suffices IsPreprimitive (stabilizer G s) s by
    apply this.isTrivialBlock_of_isBlock
    -- `IsBlock (Subtype.val ⁻¹' B : Set s)`
    let φ' : stabilizer G s → G := Subtype.val
    let f' : s →ₑ[φ'] α := {
      toFun := Subtype.val
      map_smul' _ _ := rfl }
    apply MulAction.IsBlock.preimage f' hB
  infer_instance

variable [Finite α]
/-
**MulAction.IsBlock.compl_subset_of_stabilizer_le_of_not_subset_of_not_subset_co
mpl** 是 Mathlib 中的一个引理，位于命名空间 `MulAction.IsBlock`。
形式化陈述：compl_subset_of_stabilizer_le_of_not_subset_of_not_subset_compl [IsMultipl
yPretransitive M α (s.ncard + 1)] {G : Subgroup M} (hG : stabilizer M s <= G) {B
 : Set α} (hBs : ¬ B subseteq s) (hBsc : ¬ B subseteq sᶜ) (hB : IsBlock G B) : s
ᶜ subseteq B
参数：s.ncard + 1；hG : stabilizer M s <= G；hBs : ¬ B subseteq s；hBsc : ¬ B subseteq
 sᶜ；hB : IsBlock G B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.is_one_pretransitive_iff`：is_one_pretransitive_iff : IsMultipl
yPretransitive G α 1 ↔ IsPretransitive G α
· 使用定理 `SubMulAction.ofFixingSubgroup.isMultiplyPretransitive`：∀ (G : Type u_1) 
{α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] {m n : ℕ}   [Hn : MulAc
tion.IsMultiplyPretransitive G α n] (s : Se…
· 使用定理 `MulAction.IsPretransitive.exists_smul_eq`：∀ {M : Type u_5} {α : Type u_6
} {inst : SMul M α} [self : MulAction.IsPretransitive M α] (x y : α), ∃ g, g • x
 = y
· 使用定理 `SubMulAction.val_smul`：val_smul (r : R) (x : p) : (↑(r • x) : M) = r • (
x : M)
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MulAction.isBlock_iff_smul_eq_of_nonempty`：isBlock_iff_smul_eq_of_nonemp
ty : IsBlock G B ↔ forall ⦃g : G⦄, (g • B inter B).Nonempty -> g • B = B
· 使用定理 `MulAction.fixingSubgroup_le_stabilizer`：MulAction.fixingSubgroup_le_stab
ilizer (s : Set α) : fixingSubgroup G s <= stabilizer G s
· 使用定理 `mem_fixingSubgroup_iff`：mem_fixingSubgroup_iff {s : Set α} {m : M} : m i
n fixingSubgroup M s ↔ forall y in s, m • y = y
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
lemma compl_subset_of_stabilizer_le_of_not_subset_of_not_subset_compl
    [IsMultiplyPretransitive M α (s.ncard + 1)]
    {G : Subgroup M} (hG : stabilizer M s ≤ G)
    {B : Set α}
    (hBs : ¬ B ⊆ s) (hBsc : ¬ B ⊆ sᶜ) (hB : IsBlock G B) :
    sᶜ ⊆ B := by
  have : ∃ a : α, a ∈ B ∧ a ∈ s := by grind
  obtain ⟨a, ha, ha'⟩ := this
  have : ∃ b : α, b ∈ B ∧ b ∈ sᶜ := by grind
  obtain ⟨b, hb, hb'⟩ := this
  intro x hx'
  suffices ∃ k : fixingSubgroup M s, k • b = x by
    obtain ⟨⟨k, hk⟩, rfl⟩ := this
    suffices k • B = B from this.le (smul_mem_smul_set hb)
    -- `k • B = B`
    apply isBlock_iff_smul_eq_of_nonempty.mp hB (g := ⟨k, ?_⟩)
    · refine ⟨a, ?_, ha⟩
      rw [mem_fixingSubgroup_iff] at hk
      rw [← hk a ha']
      exact Set.smul_mem_smul_set ha
    · -- `k ∈ G`
      apply hG
      exact MulAction.fixingSubgroup_le_stabilizer _ _ hk
  · -- `∃ (k : fixingSubgroup (Perm α) s), k • b = x`
    suffices h : IsPretransitive (fixingSubgroup M s) (ofFixingSubgroup M s) by
      obtain ⟨k, hk⟩ := h.exists_smul_eq (⟨b, hb'⟩ : ofFixingSubgroup M s) ⟨x, hx'⟩
      rw [← Subtype.coe_inj, val_smul] at hk
      exact ⟨k, hk⟩
    -- Prove pretransitivity…
    rw [← is_one_pretransitive_iff]
    apply ofFixingSubgroup.isMultiplyPretransitive M s rfl

end MulAction.IsBlock

namespace Equiv.Perm

open MulAction Equiv

variable [Finite α]

/-
**Equiv.Perm.isCoatom_stabilizer_of_ncard_lt_ncard_compl** 是 Mathlib 中的一个定理，位于命名
空间 `Equiv.Perm`。
形式化陈述：isCoatom_stabilizer_of_ncard_lt_ncard_compl {s : Set α} (h0 : s.Nonempty) 
(hα : s.ncard < sᶜ.ncard) : IsCoatom (stabilizer (Perm α) s)
参数：h0 : s.Nonempty；hα : s.ncard < sᶜ.ncard。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.ncard_univ`：∀ (α : Type u_3), Set.univ.ncard = Nat.card α
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `Set.ncard_empty`：∀ (α : Type u_3), ∅.ncard = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.stabilizer_ne_top_of_nonempty_of_nonempty_compl`：stabilizer_n
e_top_of_nonempty_of_nonempty_compl {s : Set α} (hs : s.Nonempty) (hsc : sᶜ.None
mpty) : stabilizer (Perm α) s != ⊤
· 使用定理 `stabilizer_compl`：stabilizer_compl {s : Set α} : stabilizer G sᶜ = stabi
lizer G s
· 使用定理 `Equiv.Perm.has_swap_mem_of_lt_stabilizer`：has_swap_mem_of_lt_stabilizer 
[DecidableEq α] (s : Set α) (G : Subgroup (Perm α)) (hG : stabilizer (Perm α) s 
< G) : exists g : Perm α, g.Is…
· 使用定理 `Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`：subgroup_eq_
top_of_isPreprimitive_of_isSwap_mem (hG : IsPreprimitive G α) (g : Perm α) (h2g 
: IsSwap g) (hg : g in G) : G = ⊤
· 使用定理 `Subgroup.isPretransitive_of_stabilizer_lt`：∀ {M : Type u_1} {α : Type u_
2} [inst : Group M] [inst_1 : MulAction M α] {s : Set α} {G : Subgroup M},   Mul
Action.stabilizer M s < G →    …
· 使用定理 `Equiv.Perm.exists_mem_stabilizer_smul_eq`：exists_mem_stabilizer_smul_eq 
: forall a in s, forall b in s, exists g in stabilizer (Perm α) s, g • a = b
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Set.compl_univ_iff`：compl_univ_iff {s : Set α} : sᶜ = univ ↔ s = ∅
· 使用定理 `MulAction.IsBlock.eq_univ_of_card_lt`：eq_univ_of_card_lt [hX : Finite X]
 (hB : IsBlock G B) (hB' : Nat.card X < Set.ncard B * 2) : B = Set.univ
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Set.ncard_add_ncard_compl`：ncard_add_ncard_compl (s : Set α) (hs : s.Fin
ite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `add_lt_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [Ad
dLeftStrictMono α] [AddLeftReflectLT α] (a : α) {b c : α},   a + b < a + c ↔ b <
 c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
（共 42 条，此处仅展示前 30 条）
-/
theorem isCoatom_stabilizer_of_ncard_lt_ncard_compl
    {s : Set α} (h0 : s.Nonempty) (hα : s.ncard < sᶜ.ncard) :
    IsCoatom (stabilizer (Perm α) s) := by
  classical
  have h1 : sᶜ.Nonempty := nonempty_iff_ne_empty.mpr (by aesop)
  have : Fintype α := Fintype.ofFinite α
  -- To prove that `stabilizer (Perm α) s` is maximal,
  -- we need to prove that it is `≠ ⊤`
  refine ⟨stabilizer_ne_top_of_nonempty_of_nonempty_compl h0 h1, fun G hG ↦ ?_⟩
  have hG' : stabilizer (Perm α) sᶜ < G := by rwa [stabilizer_compl]
  -- … and that every strict over-subgroup `G` is equal to `⊤`
  -- We know that `G` contains a swap
  obtain ⟨g, hg_swap, hg⟩ := has_swap_mem_of_lt_stabilizer s G hG
  -- By Jordan's theorem `subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`,
  -- it suffices to prove that `G` acts primitively
  apply subgroup_eq_top_of_isPreprimitive_of_isSwap_mem _ g hg_swap hg
  -- First, we prove that `G` acts transitively
  have := G.isPretransitive_of_stabilizer_lt hG exists_mem_stabilizer_smul_eq
  apply IsPreprimitive.mk
  -- We now have to prove that all blocks of `G` are trivial
  -- We reduce to proving that a block which is not a subsingleton is `univ`.
  intro B hB
  unfold IsTrivialBlock
  rw [or_iff_not_imp_left]
  intro hB'
  suffices sᶜ ⊆ B by
    apply hB.eq_univ_of_card_lt
    have : sᶜ.ncard ≤ B.ncard := ncard_le_ncard this
    rw [← Set.ncard_add_ncard_compl s]
    lia
  -- The proof needs 4 steps
  /- Step 1 : `sᶜ` is not a block.
       This uses that `Nat.card s < Nat.card sᶜ`.
       In the equality case, `Nat.card s` = Nat.card sᶜ`,
       it would be possible that `sᶜ` is a block,
       and then `G` would be a wreath product,
       — this is case (b) of the O'Nan-Scott classification
       of maximal subgroups of the symmetric group -/
  have not_isBlock_sc : ¬ IsBlock G sᶜ := fun hsc ↦ by
    rcases lt_or_ge (Nat.card α) (sᶜ.ncard * 2) with hB' | hB'
    · apply h0.ne_empty
      rw [← compl_univ_iff]
      exact hsc.eq_univ_of_card_lt hB'
    · rw [← not_lt] at hB'
      apply hB'
      rwa [← Set.ncard_add_ncard_compl sᶜ, mul_two, add_lt_add_iff_left, compl_compl]
  -- Step 2 : A block contained in sᶜ is a subsingleton
  have hB_not_le_sc (B : Set α) (hB : IsBlock G B) (hBsc : B ⊆ sᶜ) :
      B.Subsingleton :=
    -- uses Step 1
    hB.subsingleton_of_ssubset_of_stabilizer_Perm_le (hBsc.ssubset_of_ne (by lia)) hG'.le
  -- Step 3 : A block contained in `s` is a subsingleton
  have hB_not_le_s (B : Set α) (hB : IsBlock G B) (hBs : B ⊆ s) : B.Subsingleton :=
    have := isPreprimitive_stabilizer_subgroup hG.le
    hB.subsingleton_of_stabilizer_lt_of_subset hB_not_le_sc hG hBs
  -- Step 4 : `sᶜ ⊆ B`
  have _ := isMultiplyPretransitive α (s.ncard + 1)
  apply MulAction.IsBlock.compl_subset_of_stabilizer_le_of_not_subset_of_not_subset_compl hG.le <;>
    grind

/-- `MulAction.stabilizer (Perm α) s` is a maximal subgroup of `Perm α`,
provided `s` and `sᶜ` are nonempty, and `Nat.card α ≠ 2 * Nat.card s`.

This is the intransitive case of the O'Nan–Scott classification. -/
/-
**Equiv.Perm.isCoatom_stabilizer** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCoatom_stabilizer {s : Set α} (hs_nonempty : s.Nonempty) (hsc_nonempty :
 sᶜ.Nonempty) (hα : Nat.card α != 2 * s.ncard) : IsCoatom (stabilizer (Perm α) s
)
参数：hs_nonempty : s.Nonempty；hsc_nonempty : sᶜ.Nonempty；hα : Nat.card α != 2 * s.
ncard。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_trichotomy`：∀ (a b : ℕ), a < b ∨ a = b ∨ b < a
· 使用定理 `Equiv.Perm.isCoatom_stabilizer_of_ncard_lt_ncard_compl`：isCoatom_stabili
zer_of_ncard_lt_ncard_compl {s : Set α} (h0 : s.Nonempty) (hα : s.ncard < sᶜ.nca
rd) : IsCoatom (stabilizer (Perm α) s)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_add_ncard_compl`：ncard_add_ncard_compl (s : Set α) (hs : s.Fin
ite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `stabilizer_compl`：stabilizer_compl {s : Set α} : stabilizer G sᶜ = stabi
lizer G s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x

--- 原说明 ---
`MulAction.stabilizer (Perm α) s` is a maximal subgroup of `Perm α`,
provided `s` and `sᶜ` are nonempty, and `Nat.card α ≠ 2 * Nat.card s`.

This is the intransitive case of the O'Nan–Scott classification.
-/
theorem isCoatom_stabilizer {s : Set α}
    (hs_nonempty : s.Nonempty) (hsc_nonempty : sᶜ.Nonempty)
    (hα : Nat.card α ≠ 2 * s.ncard) :
    IsCoatom (stabilizer (Perm α) s) := by
  obtain h | h | h := Nat.lt_trichotomy s.ncard sᶜ.ncard
  · exact isCoatom_stabilizer_of_ncard_lt_ncard_compl hs_nonempty h
  · contrapose hα
    rw [← Set.ncard_add_ncard_compl s, two_mul, ← h]
  · rw [← stabilizer_compl]
    apply isCoatom_stabilizer_of_ncard_lt_ncard_compl hsc_nonempty
    rwa [compl_compl]

end Equiv.Perm

