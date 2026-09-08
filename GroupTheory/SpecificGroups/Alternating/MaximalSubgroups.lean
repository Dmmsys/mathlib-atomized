/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.Perm.MaximalSubgroups
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! # Maximal subgroups of the alternating group

* `alternatingGroup.isCoatom_stabilizer`: if neither `s : Set α` nor its complement is empty,
  and if, moreover, `Nat.card α ≠ 2 * s.ncard`,
  then `stabilizer (alternatingGroup α) s` is a maximal subgroup of `alternatingGroup α`.

This is the “intransitive case” of the O'Nan-Scott classification
of maximal subgroups of the alternating groups.

Compare with `Equiv.Perm.isCoatom_stabilizer` for the case of the permutation group.

## TODO

  * Application to primitivity of the action
    of `alternatingGroup α` on finite combinations of `α`.

  * Formalize the other cases of the classification.
    The next one should be the *imprimitive case*.

## Reference

The argument is taken from [M. Liebeck, C. Praeger, J. Saxl,
*A classification of the maximal subgroups of the finite
alternating and symmetric groups*, 1987][LiebeckPraegerSaxl-1987].

-/

public section

open scoped Pointwise

open Equiv.Perm Equiv Set MulAction

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace Equiv.Perm

/-
**Equiv.Perm.exists_mem_stabilizer_isThreeCycle_of_two_lt_ncard** 是 Mathlib 中的一个
定理，位于命名空间 `Equiv.Perm`。
形式化陈述：exists_mem_stabilizer_isThreeCycle_of_two_lt_ncard {s : Set α} (hs : 2 < n
card s) : exists g in stabilizer (Perm α) s, g.IsThreeCycle
参数：hs : 2 < ncard s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.two_lt_ncard_iff`：two_lt_ncard_iff (hs : s.Finite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `MulAction.mem_stabilizer_set_iff_subset_smul_set`：mem_stabilizer_set_iff
_subset_smul_set {s : Set α} (hs : s.Finite) : a in stabilizer G s ↔ s subseteq 
a • s
· 使用定理 `Set.subset_smul_set_iff`：subset_smul_set_iff : A subseteq a • B ↔ a⁻¹ • 
A subseteq B
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Equiv.Perm.isThreeCycle_swap_mul_swap_same`：isThreeCycle_swap_mul_swap_s
ame {a b c : α} (ab : a != b) (ac : a != c) (bc : b != c) : IsThreeCycle (swap a
 b * swap a c)
-/
theorem exists_mem_stabilizer_isThreeCycle_of_two_lt_ncard
    {s : Set α} (hs : 2 < ncard s) :
    ∃ g ∈ stabilizer (Perm α) s, g.IsThreeCycle := by
  rw [two_lt_ncard_iff] at hs
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hs
  refine ⟨swap a b * swap a c, ?_, isThreeCycle_swap_mul_swap_same hab hac hbc⟩
  rw [mem_stabilizer_set_iff_subset_smul_set s.toFinite, subset_smul_set_iff]
  rintro _ ⟨x, hx, rfl⟩
  aesop
/-
**Equiv.Perm.exists_mem_stabilizer_isThreeCycle** 是 Mathlib 中的一个定理，位于命名空间 `Equiv
.Perm`。
形式化陈述：exists_mem_stabilizer_isThreeCycle (s : Set α) (hα : 4 < Nat.card α) : exi
sts g in stabilizer (Perm α) s, g.IsThreeCycle
参数：s : Set α；hα : 4 < Nat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_or_ge`：∀ (n m : ℕ), n < m ∨ n ≥ m
· 使用定理 `Equiv.Perm.exists_mem_stabilizer_isThreeCycle_of_two_lt_ncard`：exists_me
m_stabilizer_isThreeCycle_of_two_lt_ncard {s : Set α} (hs : 2 < ncard s) : exist
s g in stabilizer (Perm α) s, g.IsThreeCycle
· 使用定理 `Set.ncard_add_ncard_compl`：ncard_add_ncard_compl (s : Set α) (hs : s.Fin
ite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `stabilizer_compl`：stabilizer_compl {s : Set α} : stabilizer G sᶜ = stabi
lizer G s
-/
theorem exists_mem_stabilizer_isThreeCycle
    (s : Set α) (hα : 4 < Nat.card α) :
    ∃ g ∈ stabilizer (Perm α) s, g.IsThreeCycle := by
  rcases Nat.lt_or_ge 2 (ncard s) with hs | hs
  · exact exists_mem_stabilizer_isThreeCycle_of_two_lt_ncard hs
  · have := ncard_add_ncard_compl s
    rw [← stabilizer_compl]
    exact exists_mem_stabilizer_isThreeCycle_of_two_lt_ncard (by grind)
/-
**Equiv.Perm.alternatingGroup_le_of_isPreprimitive** 是 Mathlib 中的一个定理，位于命名空间 `Eq
uiv.Perm`。
形式化陈述：alternatingGroup_le_of_isPreprimitive (h4 : 4 < Nat.card α) (G : Subgroup 
(Perm α)) [hG' : IsPreprimitive G α] {s : Set α} (hG : stabilizer (Perm α) s ⊓ a
lternatingGroup α <= G) : alternatingGroup α <= G
参数：h4 : 4 < Nat.card α；G : Subgroup (Perm α)；hG : stabilizer (Perm α) s ⊓ altern
atingGroup α <= G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.exists_mem_stabilizer_isThreeCycle`：exists_mem_stabilizer_isT
hreeCycle (s : Set α) (hα : 4 < Nat.card α) : exists g in stabilizer (Perm α) s,
 g.IsThreeCycle
· 使用定理 `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`：al
ternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem (hG : IsPreprimitive G α
) {g : Perm α} (h3g : IsThreeCycle g) (hg : g in G) : alte…
· 使用定理 `Equiv.Perm.IsThreeCycle.mem_alternatingGroup`：∀ {α : Type u_1} [inst : F
intype α] [inst_1 : DecidableEq α] {f : Equiv.Perm α}, f.IsThreeCycle → f ∈ alte
rnatingGroup α
-/
theorem alternatingGroup_le_of_isPreprimitive (h4 : 4 < Nat.card α)
    (G : Subgroup (Perm α)) [hG' : IsPreprimitive G α] {s : Set α}
    (hG : stabilizer (Perm α) s ⊓ alternatingGroup α ≤ G) :
    alternatingGroup α ≤ G := by
  -- G contains a three_cycle
  obtain ⟨g, hg, hg3⟩ := exists_mem_stabilizer_isThreeCycle s h4
  -- By Jordan's theorem, it suffices to prove that G acts primitively
  apply alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG' hg3
  exact hG ⟨hg, IsThreeCycle.mem_alternatingGroup hg3⟩

end Equiv.Perm

namespace alternatingGroup

/-
**alternatingGroup.stabilizer.surjective_toPerm** 是 Mathlib 中的一个定理，位于命名空间 `alter
natingGroup.stabilizer`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {s : Set α}, 
  sᶜ.Nontrivial → Function.Surjective MulAction.toPerm
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.swap_isSwap_iff`：swap_isSwap_iff {a b : α} : (swap a b).IsSwa
p ↔ a != b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Equiv.Perm.support_swap`：support_swap {x y : α} (h : x != y) : support (
swap x y) = {x, y}
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用引理 `MulAction.mem_stabilizer_set_iff_smul_set_subset`：mem_stabilizer_set_iff
_smul_set_subset {s : Set α} (hs : s.Finite) : a in stabilizer G s ↔ a • s subse
teq s
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Equiv.Perm.smul_def`：∀ {α : Type u_6} (f : Equiv.Perm α) (a : α), f • a 
= f a
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用引理 `Int.units_eq_one_or`：units_eq_one_or (u : Intˣ) : u = 1 ∨ u = -1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.sign_ofSubtype`：sign_ofSubtype {p : α -> Prop} [DecidablePred
 p] [Fintype (Subtype p)] (f : Equiv.Perm (Subtype p)) : sign (ofSubtype f) = si
gn f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Submonoid.mk_smul`：mk_smul (g : M') (hg : g in S) (a : α) : (⟨g, hg⟩ : S
) • a = g • a
· 使用定理 `Equiv.Perm.ofSubtype_mem_stabilizer`：ofSubtype_mem_stabilizer [Decidable
Pred fun x => x in s] (g : Perm s) : g.ofSubtype in stabilizer (Perm α) s
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
（共 39 条，此处仅展示前 30 条）
-/
theorem stabilizer.surjective_toPerm {s : Set α} (hs : sᶜ.Nontrivial) :
    Function.Surjective (toPerm : stabilizer (alternatingGroup α) s → Perm s) := by
  classical
  have : ∃ k : Perm α, IsSwap k ∧ _root_.Disjoint s k.support := by
    obtain ⟨a, ha, b, hb, hab⟩ := hs
    use Equiv.swap a b
    rw [swap_isSwap_iff]; aesop
  obtain ⟨k, hk_swap, hk_support⟩ := this
  have hks : k • s = s := by
    rw [← mem_stabilizer_iff, mem_stabilizer_set_iff_smul_set_subset s.toFinite]
    intro _
    simp only [mem_smul_set]
    rintro ⟨x, hx, rfl⟩
    convert! hx
    rw [Perm.smul_def, ← Perm.notMem_support]
    exact (Set.disjoint_left.mp hk_support) hx
  intro g
  rcases Int.units_eq_one_or (sign g) with hsg | hsg
  · use! Equiv.Perm.ofSubtype g
    · simp [mem_alternatingGroup, hsg]
    · rw [mem_stabilizer_iff, Submonoid.mk_smul]
      exact ofSubtype_mem_stabilizer g
    · aesop
  · use! Equiv.Perm.ofSubtype g * k
    · simp [mem_alternatingGroup, hk_swap.sign_eq, hsg]
    · rw [mem_stabilizer_iff, Submonoid.mk_smul, mul_smul, hks, ofSubtype_mem_stabilizer]
    · ext x
      suffices k x = x by simp [this]
      rw [Set.disjoint_left] at hk_support
      rw [← notMem_support]
      exact hk_support x.prop

/-- In the alternating group, the stabilizer of a set acts
primitively on that set if the complement is nontrivial. -/
/-
**alternatingGroup.stabilizer_isPreprimitive** 是 Mathlib 中的一个定理，位于命名空间 `alternat
ingGroup`。
形式化陈述：stabilizer_isPreprimitive {s : Set α} (hs : (sᶜ : Set α).Nontrivial) : IsP
reprimitive (stabilizer (alternatingGroup α) s) s
参数：hs : (sᶜ : Set α).Nontrivial。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.isPreprimitive_stabilizer_of_surjective`：isPreprimitive_stabil
izer_of_surjective (hs : Function.Surjective (toPerm : stabilizer M s -> Perm s)
) : IsPreprimitive (stabilizer M s) s
· 使用定理 `alternatingGroup.stabilizer.surjective_toPerm`：∀ {α : Type u_1} [inst : 
Fintype α] [inst_1 : DecidableEq α] {s : Set α},   sᶜ.Nontrivial → Function.Surj
ective MulAction.toPerm

--- 原说明 ---
In the alternating group, the stabilizer of a set acts
primitively on that set if the complement is nontrivial.
-/
theorem stabilizer_isPreprimitive {s : Set α} (hs : (sᶜ : Set α).Nontrivial) :
    IsPreprimitive (stabilizer (alternatingGroup α) s) s :=
  isPreprimitive_stabilizer_of_surjective s (stabilizer.surjective_toPerm hs)

/-- A subgroup of the alternating group that contains
the stabilizer of a set acts primitively on that set
if the complement is nontrivial. -/
/-
**alternatingGroup.stabilizer_subgroup_isPreprimitive** 是 Mathlib 中的一个定理，位于命名空间 
`alternatingGroup`。
形式化陈述：stabilizer_subgroup_isPreprimitive {s : Set α} (hsc : sᶜ.Nontrivial) {G : 
Subgroup (alternatingGroup α)} (hG : stabilizer (alternatingGroup α) s <= G) : I
sPreprimitive (stabilizer G s) s
参数：hsc : sᶜ.Nontrivial；alternatingGroup α；hG : stabilizer (alternatingGroup α) s
 <= G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `alternatingGroup.stabilizer_isPreprimitive`：stabilizer_isPreprimitive {s
 : Set α} (hs : (sᶜ : Set α).Nontrivial) : IsPreprimitive (stabilizer (alternati
ngGroup α) s) s
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `MulAction.IsPreprimitive.of_surjective`：∀ {M : Type u_3} [inst : Group M
] {α : Type u_4} [inst_1 : MulAction M α] {N : Type u_5} {β : Type u_6}   [inst_
2 : Group N] [inst_3 : MulAc…
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id

--- 原说明 ---
A subgroup of the alternating group that contains
the stabilizer of a set acts primitively on that set
if the complement is nontrivial.
-/
theorem stabilizer_subgroup_isPreprimitive {s : Set α} (hsc : sᶜ.Nontrivial)
    {G : Subgroup (alternatingGroup α)} (hG : stabilizer (alternatingGroup α) s ≤ G) :
    IsPreprimitive (stabilizer G s) s :=
  have := stabilizer_isPreprimitive hsc
  let φ (g : stabilizer (alternatingGroup α) s) : stabilizer G s :=
      ⟨⟨g, hG g.prop⟩, g.prop⟩
  let f : s →ₑ[φ] s := {
      toFun := id
      map_smul' _ _ := rfl }
  IsPreprimitive.of_surjective (f := f) Function.surjective_id

/-- If `s : Set α` is nonempty and its complement has at least two elements,
then `stabilizer (alternatingGroup α) s ≠ ⊤`. -/
/-
**alternatingGroup.stabilizer_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `alternatingGroup
`。
形式化陈述：stabilizer_ne_top {s : Set α} (hs : s.Nonempty) (hsc : sᶜ.Nontrivial) : st
abilizer (alternatingGroup α) s != ⊤
参数：hs : s.Nonempty；hsc : sᶜ.Nontrivial。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sign_mul`：sign_mul (f g : Perm α) : sign (f * g) = sign f * s
ign g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.Perm.sign_swap'`：sign_swap' {x y : α} : sign (swap x y) = if x = y
 then 1 else -1
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If `s : Set α` is nonempty and its complement has at least two elements,
then `stabilizer (alternatingGroup α) s ≠ ⊤`.
-/
theorem stabilizer_ne_top {s : Set α} (hs : s.Nonempty) (hsc : sᶜ.Nontrivial) :
    stabilizer (alternatingGroup α) s ≠ ⊤ := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb, c, hc, hbc⟩ := hsc
  suffices ∃ g, g ∉ stabilizer (alternatingGroup α) s by contrapose! this; simp [this]
  use ⟨Equiv.swap a b * Equiv.swap a c, by aesop⟩
  simp_rw [mem_stabilizer_set, Subgroup.mk_smul, mul_smul, Perm.smul_def]
  grind

/-- Here, we need that `Nat.card α` has at least `4` elements,
so that  either `t` has at least 3 elements, or `tᶜ` has at least 2.
The condition is necessary, because the result is wrong when
`α = {1, 2, 3}` and either `t = {1, 2}` or `t = {1}`. -/
/-
**alternatingGroup.exists_mem_stabilizer_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `alte
rnatingGroup`。
形式化陈述：exists_mem_stabilizer_smul_eq (hα : 4 <= Nat.card α) {t : Set α} : forall 
a in t, forall b in t, exists g in stabilizer (alternatingGroup α) t, g • a = b
参数：hα : 4 <= Nat.card α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.sdiff_nonempty_of_ncard_lt_ncard`：sdiff_nonempty_of_ncard_lt_ncard (
h : s.ncard < t.ncard) (hs : s.Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_pair`：ncard_pair {a b : α} (h : a != b) : ({a, b} : Set α).nca
rd = 2
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.Perm.sign_mul`：sign_mul (f g : Perm α) : sign (f * g) = sign f * s
ign g
· 使用定理 `Equiv.Perm.sign_swap'`：sign_swap' {x y : α} : sign (swap x y) = if x = y
 then 1 else -1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MulAction.mem_stabilizer_set'`：mem_stabilizer_set' {s : Set α} (hs : s.F
inite) : a in stabilizer G s ↔ forall ⦃b⦄, b in s -> a • b in s
· 使用定理 `Set.ncard_add_ncard_compl`：ncard_add_ncard_compl (s : Set α) (hs : s.Fin
ite
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.one_lt_ncard_iff`：one_lt_ncard_iff (hs : s.Finite

--- 原说明 ---
Here, we need that `Nat.card α` has at least `4` elements,
so that  either `t` has at least 3 elements, or `tᶜ` has at least 2.
The condition is necessary, because the result is wrong when
`α = {1, 2, 3}` and either `t = {1, 2}` or `t = {1}`.
-/
theorem exists_mem_stabilizer_smul_eq (hα : 4 ≤ Nat.card α) {t : Set α} :
    ∀ a ∈ t, ∀ b ∈ t, ∃ g ∈ stabilizer (alternatingGroup α) t, g • a = b := by
  intro a ha b hb
  by_cases hab : a = b
  · use 1
    simpa
  by_cases ht : 2 < t.ncard
  · rw [← Set.ncard_pair hab] at ht
    replace ht := Set.sdiff_nonempty_of_ncard_lt_ncard ht
    obtain ⟨c, hct, hc⟩ := ht
    simp only [mem_insert_iff, not_or] at hc
    refine ⟨⟨swap c a * swap a b, by simp [hab, hc.1]⟩, ?_, ?_⟩
    · simp only [mem_stabilizer_set' t.toFinite, Subgroup.mk_smul, Perm.smul_def, coe_mul]
      grind
    · simp only [Subgroup.mk_smul, Perm.smul_def, coe_mul]
      grind
  · have := ncard_add_ncard_compl t
    obtain ⟨c, d, hc, hd, hcd⟩ := (one_lt_ncard_iff tᶜ.toFinite).mp (by grind)
    refine ⟨⟨swap a b * swap c d, by simp [hab, hcd]⟩, ?_, ?_⟩
    · simp only [mem_stabilizer_set' t.toFinite, Subgroup.mk_smul, Perm.smul_def, coe_mul]
      grind
    · simp only [Subgroup.smul_def, Perm.smul_def, Perm.coe_mul]
      grind
/-
**alternatingGroup.subgroup_eq_top_of_isPreprimitive** 是 Mathlib 中的一个定理，位于命名空间 `
alternatingGroup`。
形式化陈述：subgroup_eq_top_of_isPreprimitive (h4 : 4 < Nat.card α) (G : Subgroup (alt
ernatingGroup α)) [hG' : IsPreprimitive G α] {s : Set α} (hG : stabilizer (alter
natingGroup α) s <= G) : G = ⊤
参数：h4 : 4 < Nat.card α；G : Subgroup (alternatingGroup α)；hG : stabilizer (altern
atingGroup α) s <= G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.exists_mem_stabilizer_isThreeCycle`：exists_mem_stabilizer_isT
hreeCycle (s : Set α) (hα : 4 < Nat.card α) : exists g in stabilizer (Perm α) s,
 g.IsThreeCycle
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.map_subtype_le_map_subtype`：map_subtype_le_map_subtype {G' : Su
bgroup G} {H K : Subgroup G'} : H.map G'.subtype <= K.map G'.subtype ↔ H <= K
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
· 使用定理 `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`：al
ternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem (hG : IsPreprimitive G α
) {g : Perm α} (h3g : IsThreeCycle g) (hg : g in G) : alte…
· 使用定理 `MulAction.isPreprimitive_congr`：isPreprimitive_congr (hφ : Function.Surj
ective φ) (hf : Function.Bijective f) : IsPreprimitive M α ↔ IsPreprimitive N β
· 使用定理 `MonoidHom.subgroupMap_surjective`：subgroupMap_surjective (f : G ->* G') 
(H : Subgroup G) : Function.Surjective (f.subgroupMap H)
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
· 使用定理 `Equiv.Perm.IsThreeCycle.mem_alternatingGroup`：∀ {α : Type u_1} [inst : F
intype α] [inst_1 : DecidableEq α] {f : Equiv.Perm α}, f.IsThreeCycle → f ∈ alte
rnatingGroup α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem subgroup_eq_top_of_isPreprimitive (h4 : 4 < Nat.card α)
    (G : Subgroup (alternatingGroup α)) [hG' : IsPreprimitive G α] {s : Set α}
    (hG : stabilizer (alternatingGroup α) s ≤ G) :
    G = ⊤ := by
  obtain ⟨g, hg, hg3⟩ := exists_mem_stabilizer_isThreeCycle s h4
  rw [eq_top_iff, ← Subgroup.map_subtype_le_map_subtype,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  -- By Jordan's theorem, it suffices to prove that G acts primitively
  apply alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem _ hg3
  · use ⟨g, hg3.mem_alternatingGroup⟩
    simpa only [SetLike.mem_coe, Subgroup.subtype_apply, and_true] using hG hg
  · let φ := (alternatingGroup α).subtype.subgroupMap G
    let f : α →ₑ[φ] α := {
      toFun := id
      map_smul' _ _ := rfl }
    rwa [← isPreprimitive_congr (f := f) ((alternatingGroup α).subtype.subgroupMap_surjective G)
      Function.bijective_id]

end alternatingGroup

namespace MulAction.IsBlock

open alternatingGroup

/-
**MulAction.IsBlock.subsingleton_of_ssubset_compl_of_stabilizer_alternatingGroup
_le** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock`。
形式化陈述：subsingleton_of_ssubset_compl_of_stabilizer_alternatingGroup_le {s B : Set
 α} {G : Subgroup (alternatingGroup α)} (hs : s.Nontrivial) (hB_ss_sc : B ⊂ sᶜ) 
(hG : stabilizer (alternatingGroup α) s <= G) (hB : IsBlock G B) : B.Subsingleto
n
参数：alternatingGroup α；hs : s.Nontrivial；hB_ss_sc : B ⊂ sᶜ；hG : stabilizer (alter
natingGroup α) s <= G；hB : IsBlock G B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.IsBlock.subsingleton_of_ssubset_of_stabilizer_le`：subsingleton
_of_ssubset_of_stabilizer_le {B : Set α} (hB_ss_sc : B ⊂ s) (hB : IsBlock M B) (
hG : Function.Surjective (MulAction.toPerm : sta…
· 使用定理 `alternatingGroup.stabilizer.surjective_toPerm`：∀ {α : Type u_1} [inst : 
Fintype α] [inst_1 : DecidableEq α] {s : Set α},   sᶜ.Nontrivial → Function.Surj
ective MulAction.toPerm
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `stabilizer_compl`：stabilizer_compl {s : Set α} : stabilizer G sᶜ = stabi
lizer G s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subsingleton_of_ssubset_compl_of_stabilizer_alternatingGroup_le
    {s B : Set α} {G : Subgroup (alternatingGroup α)}
    (hs : s.Nontrivial) (hB_ss_sc : B ⊂ sᶜ) (hG : stabilizer (alternatingGroup α) s ≤ G)
    (hB : IsBlock G B) :
    B.Subsingleton := by
  apply hB.subsingleton_of_ssubset_of_stabilizer_le hB_ss_sc
  intro g
  obtain ⟨⟨k, hk⟩, rfl⟩ := alternatingGroup.stabilizer.surjective_toPerm (by rwa [compl_compl]) g
  rw [stabilizer_compl] at hk
  exact ⟨⟨⟨k, hG hk⟩, by aesop⟩, rfl⟩

end MulAction.IsBlock

namespace alternatingGroup

/-- Note : The proof of this statement is close to that
of `Equiv.Perm.isCoatom_stabilizer_of_ncard_lt_ncard_compl`,
and while it would not be absolutely impossible to abstract both proofs,
the result would be slightly awkward because the
details of the results involved in the proof differ in annoying details.
And it would be used only twice. -/
/-
**alternatingGroup.isCoatom_stabilizer_of_ncard_lt_ncard_compl** 是 Mathlib 中的一个定
理，位于命名空间 `alternatingGroup`。
形式化陈述：isCoatom_stabilizer_of_ncard_lt_ncard_compl {s : Set α} (h0 : s.Nontrivial
) (hs : s.ncard < (sᶜ : Set α).ncard) : IsCoatom (stabilizer (alternatingGroup α
) s)
参数：h0 : s.Nontrivial；hs : s.ncard < (sᶜ : Set α).ncard。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ncard_add_ncard_compl`：ncard_add_ncard_compl (s : Set α) (hs : s.Fin
ite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.one_lt_ncard_iff_nontrivial`：one_lt_ncard_iff_nontrivial [Finite s] 
: 1 < s.ncard ↔ s.Nontrivial
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Set.Nonempty.ncard_pos`：∀ {α : Type u_1} {s : Set α}, autoParam s.Finite
 Set.ncard_pos._auto_1 → s.Nonempty → 0 < s.ncard
· 使用定理 `Set.Nontrivial.nonempty`：∀ {α : Type u} {s : Set α}, s.Nontrivial → s.No
nempty
· 使用定理 `alternatingGroup.stabilizer_ne_top`：stabilizer_ne_top {s : Set α} (hs : 
s.Nonempty) (hsc : sᶜ.Nontrivial) : stabilizer (alternatingGroup α) s != ⊤
· 使用定理 `Subgroup.isPretransitive_of_stabilizer_lt`：∀ {M : Type u_1} {α : Type u_
2} [inst : Group M] [inst_1 : MulAction M α] {s : Set α} {G : Subgroup M},   Mul
Action.stabilizer M s < G →    …
· 使用定理 `alternatingGroup.exists_mem_stabilizer_smul_eq`：exists_mem_stabilizer_sm
ul_eq (hα : 4 <= Nat.card α) {t : Set α} : forall a in t, forall b in t, exists 
g in stabilizer (alternatingGroup α)…
· 使用定理 `Nat.le_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n ≤ m
· 使用定理 `MulAction.IsTrivialBlock.eq_1`：∀ {X : Type u_2} (B : Set X), MulAction.I
sTrivialBlock B = (B.Subsingleton ∨ B = Set.univ)
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_ne_univ`：compl_ne_univ : sᶜ != univ ↔ s.Nonempty
· 使用定理 `MulAction.IsBlock.eq_univ_of_card_lt`：eq_univ_of_card_lt [hX : Finite X]
 (hB : IsBlock G B) (hB' : Nat.card X < Set.ncard B * 2) : B = Set.univ
· 使用定理 `MulAction.IsBlock.subsingleton_of_ssubset_compl_of_stabilizer_alternatin
gGroup_le`：subsingleton_of_ssubset_compl_of_stabilizer_alternatingGroup_le {s B 
: Set α} {G : Subgroup (alternatingGroup α)} (hs : s.Nontrivial) (hB_ss…
· 使用定理 `LE.le.ssubset_of_ne`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a ⊆ b → a ≠ b → a ⊂ b
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `alternatingGroup.stabilizer_subgroup_isPreprimitive`：stabilizer_subgroup
_isPreprimitive {s : Set α} (hsc : sᶜ.Nontrivial) {G : Subgroup (alternatingGrou
p α)} (hG : stabilizer (alternatingGroup …
· 使用引理 `MulAction.IsBlock.subsingleton_of_stabilizer_lt_of_subset`：subsingleton_
of_stabilizer_lt_of_subset {B : Set α} {G : Subgroup M} [IsPreprimitive (stabili
zer G s) s] (hB : IsBlock G B) (hB_not_le_sc : …
· 使用定理 `alternatingGroup.isMultiplyPretransitive`：∀ (α : Type u_1) [inst : Finty
pe α] [inst_1 : DecidableEq α],   MulAction.IsMultiplyPretransitive (↥(alternati
ngGroup α)) α (Nat.card α - 2)
· 使用定理 `MulAction.isMultiplyPretransitive_of_le`：isMultiplyPretransitive_of_le {
m n : Nat} [IsMultiplyPretransitive G α n] (hmn : m <= n) (hα : n <= Nat.card α)
 [Finite α] : IsMultiplyPretr…
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Note : The proof of this statement is close to that
of `Equiv.Perm.isCoatom_stabilizer_of_ncard_lt_ncard_compl`,
and while it would not be absolutely impossible to abstract both proofs,
the result would be slightly awkward because the
details of the results involved in the proof differ in annoying details.
And it would be used only twice.
-/
theorem isCoatom_stabilizer_of_ncard_lt_ncard_compl {s : Set α}
    (h0 : s.Nontrivial) (hs : s.ncard < (sᶜ : Set α).ncard) :
    IsCoatom (stabilizer (alternatingGroup α) s) := by
  have := ncard_add_ncard_compl s
  have h1 : sᶜ.Nontrivial := by
    rw [← one_lt_ncard_iff_nontrivial]
    exact lt_of_le_of_lt h0.nonempty.ncard_pos hs
  have hα : 4 < Nat.card α := by
    rw [← Set.one_lt_ncard_iff_nontrivial] at h0
    grind
  -- To prove that `stabilizer (alternatingGroup α) s` is maximal,
  -- we need to prove that it is `≠ ⊤`
  use stabilizer_ne_top h0.nonempty h1
  -- … and that every strict over-subgroup `G` is equal to `⊤`
  intro G hG
  suffices IsPreprimitive G α from subgroup_eq_top_of_isPreprimitive hα G hG.le
  -- G acts transitively
  have := G.isPretransitive_of_stabilizer_lt hG
    (exists_mem_stabilizer_smul_eq (Nat.le_of_succ_le hα))
  apply IsPreprimitive.mk
  -- We reduce to proving that a block which is not a subsingleton is `univ`.
  intro B hB
  rw [IsTrivialBlock, or_iff_not_imp_left]
  intro hB'
  suffices sᶜ ⊆ B by
    apply hB.eq_univ_of_card_lt
    have : sᶜ.ncard ≤ B.ncard := ncard_le_ncard this
    grind
  -- The proof needs 4 steps
  /- Step 1 : `sᶜ` is not a block.
       This uses that `s.ncard  < sᶜ.ncard`.
       In the equality case, it is possible that `B = sᶜ` is a block:
       in that case, `G` would be a wreath product,
       this is case (b) of the O'Nan-Scott classification
       of maximal subgroups of the alternating group. -/
  have not_isBlock_sc : ¬ IsBlock G sᶜ := fun hsc ↦ by
    apply compl_ne_univ.mpr h0.nonempty -- `sᶜ ≠ univ`
    apply hsc.eq_univ_of_card_lt
    grind
  -- Step 2 : A block contained in `sᶜ` is a subsingleton
  have hB_not_le_sc (B : Set α) (hB : IsBlock G B) (hBsc : B ⊆ sᶜ) :
      B.Subsingleton :=
    IsBlock.subsingleton_of_ssubset_compl_of_stabilizer_alternatingGroup_le h0
      (hBsc.ssubset_of_ne (by aesop)) -- uses Step 1
      hG.le hB
  -- Step 3 : A block contained in `s` is a subsingleton
  have hB_not_le_s (B : Set α) (hB : IsBlock G B) (hBs : B ⊆ s) :
      B.Subsingleton :=
    have : IsPreprimitive (stabilizer G s) s :=
      stabilizer_subgroup_isPreprimitive h1 hG.le
    hB.subsingleton_of_stabilizer_lt_of_subset hB_not_le_sc hG hBs
  -- Step 4 : sᶜ ⊆ B : A block which is not a subsingleton contains `sᶜ`.
  suffices IsMultiplyPretransitive (↥(alternatingGroup α)) α (s.ncard + 1) by
    have : ¬ B ⊆ s := fun h ↦ hB' (hB_not_le_s B hB h)
    have : ¬ B ⊆ sᶜ := fun h ↦ hB' (hB_not_le_sc B hB h)
    apply hB.compl_subset_of_stabilizer_le_of_not_subset_of_not_subset_compl
      hG.le <;> grind
  have := isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) _ (Nat.sub_le _ _)
  grind
/-
**alternatingGroup.isCoatom_stabilizer_singleton** 是 Mathlib 中的一个定理，位于命名空间 `alte
rnatingGroup`。
形式化陈述：isCoatom_stabilizer_singleton (h3 : 3 <= Nat.card α) {s : Set α} (h : s.No
nempty) (h1 : s.Subsingleton) : IsCoatom (stabilizer (alternatingGroup α) s)
参数：h3 : 3 <= Nat.card α；h : s.Nonempty；h1 : s.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finite.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial [Finite α]
 : 1 < Nat.card α ↔ Nontrivial α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.Subsingleton.eq_singleton_of_mem`：∀ {α : Type u} {s : Set α}, s.Subs
ingleton → ∀ {x : α}, x ∈ s → s = {x}
· 使用引理 `MulAction.stabilizer_singleton`：stabilizer_singleton (b : α) : stabilize
r G ({b} : Set α) = stabilizer G b
· 使用定理 `alternatingGroup.isPreprimitive_of_three_le_card`：∀ (α : Type u_1) [inst
 : Fintype α] [inst_1 : DecidableEq α],   3 ≤ Nat.card α → MulAction.IsPreprimit
ive (↥(alternatingGroup α)) α
· 使用定理 `MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive`：∀ (G : T
ype u_3) [inst : Group G] {X : Type u_4} [inst_1 : MulAction G X] [Nontrivial X]
 [MulAction.IsPreprimitive G X]   (a : X), IsCoatom …
-/
theorem isCoatom_stabilizer_singleton (h3 : 3 ≤ Nat.card α)
    {s : Set α} (h : s.Nonempty) (h1 : s.Subsingleton) :
    IsCoatom (stabilizer (alternatingGroup α) s) := by
  have : Nontrivial α := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    grind
  obtain ⟨a, ha⟩ := h
  rw [Subsingleton.eq_singleton_of_mem h1 ha, stabilizer_singleton]
  have : IsPreprimitive (alternatingGroup α) α :=
    alternatingGroup.isPreprimitive_of_three_le_card α h3
  apply IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive

/-- `MulAction.stabilizer (alternatingGroup α) s` is a maximal subgroup of `alternatingGroup α`,
provided `s ≠ ∅`, `sᶜ ≠ ∅` and `Nat.card α ≠ 2 * s.ncard`.

This is the intransitive case of the O'Nan–Scott classification. -/
/-
**alternatingGroup.isCoatom_stabilizer** 是 Mathlib 中的一个定理，位于命名空间 `alternatingGro
up`。
形式化陈述：isCoatom_stabilizer {s : Set α} (h0 : s.Nonempty) (h1 : sᶜ.Nonempty) (hs :
 Nat.card α != 2 * ncard s) : IsCoatom (stabilizer (alternatingGroup α) s)
参数：h0 : s.Nonempty；h1 : sᶜ.Nonempty；hs : Nat.card α != 2 * ncard s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `alternatingGroup.isCoatom_stabilizer_of_ncard_lt_ncard_compl`：isCoatom_s
tabilizer_of_ncard_lt_ncard_compl {s : Set α} (h0 : s.Nontrivial) (hs : s.ncard 
< (sᶜ : Set α).ncard) : IsCoatom (stabilizer (alte…
· 使用定理 `alternatingGroup.isCoatom_stabilizer_singleton`：isCoatom_stabilizer_sing
leton (h3 : 3 <= Nat.card α) {s : Set α} (h : s.Nonempty) (h1 : s.Subsingleton) 
: IsCoatom (stabilizer (alternatingG…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_add_ncard_compl`：ncard_add_ncard_compl (s : Set α) (hs : s.Fin
ite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.ncard_pos`：ncard_pos (hs : s.Finite
· 使用定理 `Nat.add_left_cancel_iff`：∀ {m k n : ℕ}, n + m = n + k ↔ m = k
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `stabilizer_compl`：stabilizer_compl {s : Set α} : stabilizer G sᶜ = stabi
lizer G s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x

--- 原说明 ---
`MulAction.stabilizer (alternatingGroup α) s` is a maximal subgroup of `alternat
ingGroup α`,
provided `s ≠ ∅`, `sᶜ ≠ ∅` and `Nat.card α ≠ 2 * s.ncard`.

This is the intransitive case of the O'Nan–Scott classification.
-/
theorem isCoatom_stabilizer {s : Set α}
    (h0 : s.Nonempty) (h1 : sᶜ.Nonempty) (hs : Nat.card α ≠ 2 * ncard s) :
    IsCoatom (stabilizer (alternatingGroup α) s) := by
  rw [← ncard_add_ncard_compl s, two_mul, ne_eq, Nat.add_left_cancel_iff] at hs
  wlog hs' : ncard s < ncard sᶜ
  · rw [← stabilizer_compl]
    apply this h1 <;> rw [compl_compl] <;> grind
  · by_cases h0' : s.Nontrivial
    · apply isCoatom_stabilizer_of_ncard_lt_ncard_compl h0' hs'
    · simp only [not_nontrivial_iff] at h0'
      apply isCoatom_stabilizer_singleton _ h0 h0'
      rw [← ncard_add_ncard_compl s]
      rw [← ncard_pos] at h0 h1
      grind

end alternatingGroup

