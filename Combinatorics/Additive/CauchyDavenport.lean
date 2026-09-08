/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.Additive.ETransform
public import Mathlib.GroupTheory.Order.Min

/-!
# The Cauchy-Davenport theorem

This file proves a generalisation of the Cauchy-Davenport theorem to arbitrary groups.

Cauchy-Davenport provides a lower bound on the size of `s + t` in terms of the sizes of `s` and `t`,
where `s` and `t` are nonempty finite sets in a monoid. Precisely, it says that
`|s + t| ≥ |s| + |t| - 1` unless the RHS is bigger than the size of the smallest nontrivial subgroup
(in which case taking `s` and `t` to be that subgroup would yield a counterexample). The motivating
example is `s = {0, ..., m}`, `t = {0, ..., n}` in the integers, which gives
`s + t = {0, ..., m + n}` and `|s + t| = m + n + 1 = |s| + |t| - 1`.

There are two kinds of proof of Cauchy-Davenport:
* The first one works in linear orders by writing `a₁ < ... < aₖ` the elements of `s`,
  `b₁ < ... < bₗ` the elements of `t`, and arguing that `a₁ + b₁ < ... < aₖ + b₁ < ... < aₖ + bₗ`
  are distinct elements of `s + t`.
* The second one works in groups by performing an "e-transform". In an abelian group, the
  e-transform replaces `s` and `t` by `s ∩ g • s` and `t ∪ g⁻¹ • t`. For a suitably chosen `g`, this
  decreases `|s + t|` and keeps `|s| + |t|` the same. In a general group, we use a trickier
  e-transform (in fact, a pair of e-transforms), but the idea is the same.

## Main declarations

* `cauchy_davenport_minOrder_mul`: A generalisation of the Cauchy-Davenport theorem to arbitrary
  groups.
* `cauchy_davenport_of_isTorsionFree`: The Cauchy-Davenport theorem in torsion-free groups.
* `ZMod.cauchy_davenport`: The Cauchy-Davenport theorem for `ZMod p`.
* `cauchy_davenport_mul_of_linearOrder_isCancelMul`: The Cauchy-Davenport theorem in linear ordered
  cancellative semigroups.

## TODO

Version for `circle`.

## References

* Matt DeVos, *On a generalization of the Cauchy-Davenport theorem*

## Tags

additive combinatorics, number theory, sumset, cauchy-davenport
-/

public section

open Finset Function Monoid MulOpposite Subgroup
open scoped Pointwise

variable {G α : Type*}

/-! ### General case -/

section General
variable [Group α] [DecidableEq α] {x y : Finset α × Finset α} {s t : Finset α}

/-- The relation we induct along in the proof by DeVos of the Cauchy-Davenport theorem.
`(s₁, t₁) < (s₂, t₂)` iff
* `|s₁ * t₁| < |s₂ * t₂|`
* or `|s₁ * t₁| = |s₂ * t₂|` and `|s₂| + |t₂| < |s₁| + |t₁|`
* or `|s₁ * t₁| = |s₂ * t₂|` and `|s₁| + |t₁| = |s₂| + |t₂|` and `|s₁| < |s₂|`. -/
@[to_additive
/-- The relation we induct along in the proof by DeVos of the Cauchy-Davenport theorem.
`(s₁, t₁) < (s₂, t₂)` iff
* `|s₁ + t₁| < |s₂ + t₂|`
* or `|s₁ + t₁| = |s₂ + t₂|` and `|s₂| + |t₂| < |s₁| + |t₁|`
* or `|s₁ + t₁| = |s₂ + t₂|` and `|s₁| + |t₁| = |s₂| + |t₂|` and `|s₁| < |s₂|`. -/]
/-
**DevosMulRel** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def DevosMulRel : Finset α × Finset α → Finset α × Finset α → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· > ·) (· < ·)) on fun x ↦ (#(x.1 * x.2), #x.1 + #x.2, #x.1)

@[to_additive]
/-
**devosMulRel_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma devosMulRel_iff :
    DevosMulRel x y ↔
      #(x.1 * x.2) < #(y.1 * y.2) ∨
        #(x.1 * x.2) = #(y.1 * y.2) ∧ #y.1 + #y.2 < #x.1 + #x.2 ∨
          #(x.1 * x.2) = #(y.1 * y.2) ∧ #x.1 + #x.2 = #y.1 + #y.2 ∧ #x.1 < #y.1 := by
  simp [DevosMulRel, Prod.lex_iff, and_or_left]

@[to_additive]
/-
**devosMulRel_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma devosMulRel_of_le (mul : #(x.1 * x.2) ≤ #(y.1 * y.2))
    (hadd : #y.1 + #y.2 < #x.1 + #x.2) : DevosMulRel x y :=
  devosMulRel_iff.2 <| mul.lt_or_eq.imp_right fun h ↦ Or.inl ⟨h, hadd⟩

@[to_additive]
/-
**devosMulRel_of_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma devosMulRel_of_le_of_le (mul : #(x.1 * x.2) ≤ #(y.1 * y.2))
    (hadd : #y.1 + #y.2 ≤ #x.1 + #x.2) (hone : #x.1 < #y.1) : DevosMulRel x y :=
  devosMulRel_iff.2 <|
    mul.lt_or_eq.imp_right fun h ↦ hadd.lt_or_eq'.imp (And.intro h) fun h' ↦ ⟨h, h', hone⟩

@[to_additive]
/-
**wellFoundedOn_devosMulRel** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma wellFoundedOn_devosMulRel :
    {x : Finset α × Finset α | x.1.Nonempty ∧ x.2.Nonempty}.WellFoundedOn
      (DevosMulRel : Finset α × Finset α → Finset α × Finset α → Prop) := by
  refine wellFounded_lt.onFun.wellFoundedOn.prod_lex_of_wellFoundedOn_fiber fun n ↦
    Set.WellFoundedOn.prod_lex_of_wellFoundedOn_fiber ?_ fun n ↦
      wellFounded_lt.onFun.wellFoundedOn
  exact wellFounded_lt.onFun.wellFoundedOn.mono' fun x hx y _ ↦ tsub_lt_tsub_left_of_le <|
    add_le_add ((card_le_card_mul_right hx.1.2).trans_eq hx.2) <|
      (card_le_card_mul_left hx.1.1).trans_eq hx.2

/-- A generalisation of the **Cauchy-Davenport theorem** to arbitrary groups. The size of `s * t` is
lower-bounded by `|s| + |t| - 1` unless this quantity is greater than the size of the smallest
subgroup. -/
@[to_additive /-- A generalisation of the **Cauchy-Davenport theorem** to arbitrary groups. The
size of `s + t` is lower-bounded by `|s| + |t| - 1` unless this quantity is greater than the size
of the smallest subgroup. -/]
/-
**cauchy_davenport_minOrder_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cauchy_davenport_minOrder_mul (hs : s.Nonempty) (ht : t.Nonempty) : min (m
inOrder α) ↑(#s + #t - 1) <= #(s * t)
参数：hs : s.Nonempty；ht : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.WellFoundedOn.induction`：∀ {α : Type u_2} {r : α → α → Prop} {s : Se
t α} {x : α},   s.WellFoundedOn r → x ∈ s → ∀ {P : α → Prop}, (∀ y ∈ s, (∀ z ∈ s
, r z y → P z) → …
· 使用定理 `_private.Mathlib.Combinatorics.Additive.CauchyDavenport.0.wellFoundedOn_
devosMulRel`：∀ {α : Type u_2} [inst : Group α] [inst_1 : DecidableEq α], {x | x.
1.Nonempty ∧ x.2.Nonempty}.WellFoundedOn DevosMulRel✝
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.card_inv`：card_inv (s : Finset α) : #s⁻¹ = #s
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.Nonempty.inv`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : I
nv α] {s : Finset α}, s.Nonempty → s⁻¹.Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `_private.Mathlib.Combinatorics.Additive.CauchyDavenport.0.devosMulRel_if
f`：∀ {α : Type u_2} [inst : Group α] [inst_1 : DecidableEq α] {x y : Finset α × 
Finset α},   DevosMulRel✝ x y ↔     (x.1 * x.2).card < (y.1 * y…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finset.Nonempty.exists_eq_singleton_or_nontrivial`：∀ {α : Type u_1} {s :
 Finset α}, s.Nonempty → (∃ a, s = {a}) ∨ s.Nontrivial
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.card_singleton_mul`：card_singleton_mul (a : α) (t : Finset α) : #
({a} * t) = #t
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `inv_mul_eq_one`：inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b
（共 90 条，此处仅展示前 30 条）
-/
lemma cauchy_davenport_minOrder_mul (hs : s.Nonempty) (ht : t.Nonempty) :
    min (minOrder α) ↑(#s + #t - 1) ≤ #(s * t) := by
  -- Set up the induction on `x := (s, t)` along the `DevosMulRel` relation.
  set x := (s, t) with hx
  clear_value x
  simp only [Prod.ext_iff] at hx
  obtain ⟨rfl, rfl⟩ := hx
  refine wellFoundedOn_devosMulRel.induction (P := fun x : Finset α × Finset α ↦
    min (minOrder α) ↑(#x.1 + #x.2 - 1) ≤ #(x.1 * x.2)) ⟨hs, ht⟩ ?_
  clear! x
  rintro ⟨s, t⟩ ⟨hs, ht⟩ ih
  simp only [min_le_iff, tsub_le_iff_right, Prod.forall, Set.mem_ofPred_eq, and_imp,
    Nat.cast_le] at *
  -- If `#t < #s`, we're done by the induction hypothesis on `(t⁻¹, s⁻¹)`.
  obtain hts | hst := lt_or_ge #t #s
  · simpa only [← mul_inv_rev, add_comm, card_inv] using
      ih _ _ ht.inv hs.inv
        (devosMulRel_iff.2 <| Or.inr <| Or.inr <| by
          simpa only [← mul_inv_rev, add_comm, card_inv, true_and])
  -- If `s` is a singleton, then the result is trivial.
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, hb, hab⟩ := hs.exists_eq_singleton_or_nontrivial
  · simp [add_comm]
  -- Else, we have `a, b ∈ s` distinct. So `g := b⁻¹ * a` is a non-identity element such that `s`
  -- intersects its right translate by `g`.
  obtain ⟨g, hg, hgs⟩ : ∃ g : α, g ≠ 1 ∧ (s ∩ op g • s).Nonempty :=
    ⟨b⁻¹ * a, inv_mul_eq_one.not.2 hab.symm, _,
      mem_inter.2 ⟨ha, mem_smul_finset.2 ⟨_, hb, by simp⟩⟩⟩
  -- If `s` is equal to its right translate by `g`, then it contains a nontrivial subgroup, namely
  -- the subgroup generated by `g`. So `s * t` has size at least the size of a nontrivial subgroup,
  -- as wanted.
  obtain hsg | hsg := eq_or_ne (op g • s) s
  · have hS : (zpowers g : Set α) ⊆ a⁻¹ • (s : Set α) := by
      refine forall_mem_zpowers.2 <| @zpow_induction_right _ _ _ (· ∈ a⁻¹ • (s : Set α))
        ⟨_, ha, inv_mul_cancel _⟩ (fun c hc ↦ ?_) fun c hc ↦ ?_
      · rw [← hsg, coe_smul_finset, smul_comm]
        exact Set.smul_mem_smul_set hc
      · rwa [← op_smul_eq_mul, op_inv, ← Set.mem_smul_set_iff_inv_smul_mem, smul_comm,
          ← coe_smul_finset, hsg]
    refine Or.inl ((minOrder_le_natCard (zpowers_ne_bot.2 hg) <|
      s.finite_toSet.smul_set.subset hS).trans <| WithTop.coe_le_coe.2 <|
        ((Nat.card_mono s.finite_toSet.smul_set hS).trans_eq <| ?_).trans <|
          card_le_card_mul_right ht)
    rw [← coe_smul_finset]
    simp [-coe_smul_finset]
  -- Else, we can transform `s`, `t` to `s'`, `t'` and `s''`, `t''`, such that one of `(s', t')` and
  -- `(s'', t'')` is strictly smaller than `(s, t)` according to `DevosMulRel`.
  replace hsg : #(s ∩ op g • s) < #s := card_lt_card ⟨inter_subset_left, fun h ↦
    hsg <| eq_of_superset_of_card_ge (h.trans inter_subset_right) (card_smul_finset _ _).le⟩
  replace aux1 := card_mono <| mulETransformLeft.fst_mul_snd_subset g (s, t)
  replace aux2 := card_mono <| mulETransformRight.fst_mul_snd_subset g (s, t)
  -- If the left translate of `t` by `g⁻¹` is disjoint from `t`, then we're easily done.
  obtain hgt | hgt := disjoint_or_nonempty_inter t (g⁻¹ • t)
  · rw [← card_smul_finset g⁻¹ t]
    right
    grw [hst, ← card_union_of_disjoint hgt]
    exact (card_le_card_mul_left hgs).trans (le_add_of_le_left aux1)
  -- Else, we're done by induction on either `(s', t')` or `(s'', t'')` depending on whether
  -- `|s| + |t| ≤ |s'| + |t'|` or `|s| + |t| < |s''| + |t''|`. One of those two inequalities must
  -- hold since `2 * (|s| + |t|) = |s'| + |t'| + |s''| + |t''|`.
  obtain hstg | hstg := le_or_lt_of_add_le_add (MulETransform.card g (s, t)).ge
  · exact (ih _ _ hgs (hgt.mono inter_subset_union) <| devosMulRel_of_le_of_le aux1 hstg hsg).imp
      (WithTop.coe_le_coe.2 aux1).trans' fun h ↦ hstg.trans <| h.trans <| add_le_add_left aux1 _
  · exact (ih _ _ (hgs.mono inter_subset_union) hgt <| devosMulRel_of_le aux2 hstg).imp
      (WithTop.coe_le_coe.2 aux2).trans' fun h ↦
        hstg.le.trans <| h.trans <| add_le_add_left aux2 _

end General

/-- The **Cauchy-Davenport Theorem** for torsion-free groups. The size of `s * t` is lower-bounded
by `|s| + |t| - 1`. -/
@[to_additive
/-- The **Cauchy-Davenport theorem** for torsion-free groups. The size of `s + t` is lower-bounded
by `|s| + |t| - 1`. -/]
/-
**cauchy_davenport_of_isMulTorsionFree** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cauchy_davenport_of_isMulTorsionFree [DecidableEq G] [Group G] [IsMulTorsi
onFree G] {s t : Finset G} (hs : s.Nonempty) (ht : t.Nonempty) : #s + #t - 1 <= 
#(s * t)
参数：hs : s.Nonempty；ht : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Monoid.minOrder_eq_top`：minOrder_eq_top [IsMulTorsionFree G] : minOrder 
G = ⊤
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `cauchy_davenport_minOrder_mul`：cauchy_davenport_minOrder_mul (hs : s.Non
empty) (ht : t.Nonempty) : min (minOrder α) ↑(#s + #t - 1) <= #(s * t)
-/
lemma cauchy_davenport_of_isMulTorsionFree [DecidableEq G] [Group G] [IsMulTorsionFree G]
    {s t : Finset G} (hs : s.Nonempty) (ht : t.Nonempty) : #s + #t - 1 ≤ #(s * t) := by
  simpa only [Monoid.minOrder_eq_top, min_eq_right, le_top, Nat.cast_le]
    using cauchy_davenport_minOrder_mul hs ht

/-! ### $ℤ/nℤ$ -/

/-- The **Cauchy-Davenport Theorem**. If `s`, `t` are nonempty sets in `ℤ/pℤ`, then the size of
`s + t` is lower-bounded by `|s| + |t| - 1`, unless this quantity is greater than `p`. -/
/-
**ZMod.cauchy_davenport** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ZMod.cauchy_davenport {p : Nat} (hp : p.Prime) {s t : Finset (ZMod p)} (hs
 : s.Nonempty) (ht : t.Nonempty) : min p (#s + #t - 1) <= #(s + t)
参数：hp : p.Prime；ZMod p；hs : s.Nonempty；ht : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ZMod.minOrder_of_prime`：minOrder_of_prime {p : Nat} (hp : p.Prime) : min
Order (ZMod p) = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `cauchy_davenport_minOrder_add`：∀ {α : Type u_2} [inst : AddGroup α] [ins
t_1 : DecidableEq α] {s t : Finset α},   s.Nonempty → t.Nonempty → min (AddMonoi
d.minOrder α) ↑(s.c…

--- 原说明 ---
The **Cauchy-Davenport Theorem**. If `s`, `t` are nonempty sets in `ℤ/pℤ`, then 
the size of
`s + t` is lower-bounded by `|s| + |t| - 1`, unless this quantity is greater tha
n `p`.
-/
lemma ZMod.cauchy_davenport {p : ℕ} (hp : p.Prime) {s t : Finset (ZMod p)} (hs : s.Nonempty)
    (ht : t.Nonempty) : min p (#s + #t - 1) ≤ #(s + t) := by
  simpa only [ZMod.minOrder_of_prime hp, min_le_iff, Nat.cast_le]
    using cauchy_davenport_minOrder_add hs ht

/-! ### Linearly ordered cancellative semigroups -/

/-- The **Cauchy-Davenport Theorem** for linearly ordered cancellative semigroups. The size of
`s * t` is lower-bounded by `|s| + |t| - 1`. -/
@[to_additive
/-- The **Cauchy-Davenport theorem** for linearly ordered additive cancellative semigroups. The
size of `s + t` is lower-bounded by `|s| + |t| - 1`. -/]
/-
**cauchy_davenport_mul_of_linearOrder_isCancelMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cauchy_davenport_mul_of_linearOrder_isCancelMul [LinearOrder α] [Mul α] [I
sCancelMul α] [MulLeftMono α] [MulRightMono α] {s t : Finset α} (hs : s.Nonempty
) (ht : t.Nonempty) : #s + #t - 1 <= #(s * t)
参数：hs : s.Nonempty；ht : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem {s : Fin
set α} {a : α} : s = {a} ↔ a in s ∧ forall x in s, x = a
· 使用定理 `Finset.mem_inter`：mem_inter {a : α} {s₁ s₂ : Finset α} : a in s₁ inter s
₂ ↔ a in s₁ ∧ a in s₂
· 使用定理 `Finset.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsCancelMul.toIsRightCancelMul`：∀ {G : Type u} {inst : Mul G} [self : Is
CancelMul G], IsRightCancelMul G
· 使用定理 `LE.le.eq_of_not_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, 
a ≤ b → ¬a < b → a = b
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `lt_of_eq_of_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < 
c → a < c
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `Finset.min'_le`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (
x : α) (H2 : x ∈ s), s.min' ⋯ ≤ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_singleton_mul`：card_singleton_mul (a : α) (t : Finset α) : #
({a} * t) = #t
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `Finset.card_mul_singleton`：card_mul_singleton (s : Finset α) (a : α) : #
(s * {a}) = #s
· 使用定理 `Finset.card_union_add_card_inter`：card_union_add_card_inter (s t : Finse
t α) : #(s union t) + #(s inter t) = #s + #t
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
（共 36 条，此处仅展示前 30 条）
-/
lemma cauchy_davenport_mul_of_linearOrder_isCancelMul [LinearOrder α] [Mul α] [IsCancelMul α]
    [MulLeftMono α] [MulRightMono α]
    {s t : Finset α} (hs : s.Nonempty) (ht : t.Nonempty) : #s + #t - 1 ≤ #(s * t) := by
  suffices s * {t.min' ht} ∩ ({s.max' hs} * t) = {s.max' hs * t.min' ht} by
    rw [← card_singleton_mul (s.max' hs) t, ← card_mul_singleton s (t.min' ht),
      ← card_union_add_card_inter, ← card_singleton _, ← this, Nat.add_sub_cancel]
    exact card_mono (union_subset (mul_subset_mul_left <| singleton_subset_iff.2 <| min'_mem _ _) <|
      mul_subset_mul_right <| singleton_subset_iff.2 <| max'_mem _ _)
  refine eq_singleton_iff_unique_mem.2 ⟨mem_inter.2 ⟨mul_mem_mul (max'_mem _ _) <|
    mem_singleton_self _, mul_mem_mul (mem_singleton_self _) <| min'_mem _ _⟩, ?_⟩
  simp only [mem_inter, and_imp, mem_mul, mem_singleton, exists_eq_left,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mul_left_inj]
  exact fun a' ha' b' hb' h ↦ (le_max' _ _ ha').eq_of_not_lt fun ha ↦
    (lt_of_eq_of_lt h (mul_lt_mul_left ha _)).not_ge <| mul_le_mul_right (min'_le _ _ hb') _
