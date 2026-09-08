/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Filter.Map

/-!
# Cardinality of a set with a countable cover

Assume that a set `t` is eventually covered by a countable family of sets, all with
cardinality `≤ a`. Then `t` itself has cardinality at most `a`. This is proved in
`Cardinal.mk_subtype_le_of_countable_eventually_mem`.

Versions are also given when `t = univ`, and with `= a` instead of `≤ a`.
-/

public section

open Set Order Filter
open scoped Cardinal

namespace Cardinal

universe u v

/-- If a set `t` is eventually covered by a countable family of sets, all with cardinality at
most `a`, then the cardinality of `t` is also bounded by `a`.
Superseded by `mk_le_of_countable_eventually_mem` which does not assume
that the indexing set lives in the same universe. -/
/-
**Cardinal.mk_subtype_le_of_countable_eventually_mem_aux** 是 Mathlib 中的一个引理，位于命名
空间 `Cardinal`。
形式化陈述：mk_subtype_le_of_countable_eventually_mem_aux {α ι : Type u} {a : Cardinal
} [Countable ι] {f : ι -> Set α} {l : Filter ι} [NeBot l] {t : Set α} (ht : fora
ll x in t, forallᶠ i in l, x in f i) (h'f : forall i, #(f i) <= a) : #t <= a
参数：ht : forall x in t, forallᶠ i in l, x in f i；h'f : forall i, #(f i) <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.mk_le_iff_forall_finset_subset_card_le`：mk_le_iff_forall_finset
_subset_card_le {α : Type u} {n : Nat} {t : Set α} : #t <= n ↔ forall s : Finset
 α, (s : Set α) subseteq t -> s.card …
· 使用定理 `Finset.eventually_all`：∀ {α : Type u} {ι : Type u_2} (I : Finset ι) {l :
 Filter α} {p : ι → α → Prop},   (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x) ↔ ∀ i ∈ I, ∀ᶠ
 (x : α) in…
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Cardinal.lt_aleph0_iff_fintype`：lt_aleph0_iff_fintype {α : Type u} : #α 
< ℵ₀ ↔ Nonempty (Fintype α)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Set.mem_iUnion_of_mem`：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι
) (ha : a in s i) : a in ⋃ i, s i
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Cardinal.mk_iUnion_le_sum_mk`：mk_iUnion_le_sum_mk {α ι : Type u} {f : ι 
-> Set α} : #(⋃ i, f i) <= sum fun i => #(f i)
· 使用定理 `Cardinal.sum_le_sum`：sum_le_sum {ι} (f g : ι -> Cardinal) (H : forall i,
 f i <= g i) : sum f <= sum g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.sum_const`：sum_const (ι : Type u) (a : Cardinal.{v}) : (sum fun
 _ : ι => a) = lift.{v} #ι * lift.{u} a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If a set `t` is eventually covered by a countable family of sets, all with cardi
nality at
most `a`, then the cardinality of `t` is also bounded by `a`.
Superseded by `mk_le_of_countable_eventually_mem` which does not assume
that the indexing set lives in the same universe.
-/
lemma mk_subtype_le_of_countable_eventually_mem_aux {α ι : Type u} {a : Cardinal}
    [Countable ι] {f : ι → Set α} {l : Filter ι} [NeBot l]
    {t : Set α} (ht : ∀ x ∈ t, ∀ᶠ i in l, x ∈ f i)
    (h'f : ∀ i, #(f i) ≤ a) : #t ≤ a := by
  rcases lt_or_ge a ℵ₀ with ha | ha
  /- case `a` finite. In this case, it suffices to show that any finite subset `s` of `t` has
  cardinality at most `a`. For this, we pick `i` such that `f i` contains all the points in `s`,
  and apply the assumption that the cardinality of `f i` is at most `a`.   -/
  · obtain ⟨n, rfl⟩ : ∃ (n : ℕ), a = n := lt_aleph0.1 ha
    apply mk_le_iff_forall_finset_subset_card_le.2 (fun s hs ↦ ?_)
    have A : ∀ x ∈ s, ∀ᶠ i in l, x ∈ f i := fun x hx ↦ ht x (hs hx)
    have B : ∀ᶠ i in l, ∀ x ∈ s, x ∈ f i := (s.eventually_all).2 A
    rcases B.exists with ⟨i, hi⟩
    have : ∀ i, Fintype (f i) := fun i ↦ (lt_aleph0_iff_fintype.1 ((h'f i).trans_lt ha)).some
    let u : Finset α := (f i).toFinset
    have I1 : s.card ≤ u.card := by
      have : s ⊆ u := fun x hx ↦ by simpa only [u, Set.mem_toFinset] using hi x hx
      exact Finset.card_le_card this
    have I2 : (u.card : Cardinal) ≤ n := by
      convert! h'f i; simp only [u, Set.toFinset_card, mk_fintype]
    exact I1.trans (Nat.cast_le.1 I2)
  -- case `a` infinite:
  · have : t ⊆ ⋃ i, f i := by
      intro x hx
      obtain ⟨i, hi⟩ : ∃ i, x ∈ f i := (ht x hx).exists
      exact mem_iUnion_of_mem i hi
    calc #t ≤ #(⋃ i, f i) := mk_le_mk_of_subset this
      _ ≤ sum (fun i ↦ #(f i)) := mk_iUnion_le_sum_mk
      _ ≤ sum (fun _ ↦ a) := sum_le_sum _ _ h'f
      _ = #ι * a := by simp
      _ ≤ ℵ₀ * a := by grw [mk_le_aleph0]
      _ = a := aleph0_mul_eq ha

/-- If a set `t` is eventually covered by a countable family of sets, all with cardinality at
most `a`, then the cardinality of `t` is also bounded by `a`. -/
/-
**Cardinal.mk_subtype_le_of_countable_eventually_mem** 是 Mathlib 中的一个引理，位于命名空间 `
Cardinal`。
形式化陈述：mk_subtype_le_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : C
ardinal} [Countable ι] {f : ι -> Set α} {l : Filter ι} [NeBot l] {t : Set α} (ht
 : forall x in t, forallᶠ i in l, x in f i) (h'f : forall i, #(f i) <= a) : #t <
= a
参数：ht : forall x in t, forallᶠ i in l, x in f i；h'f : forall i, #(f i) <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.mk_subtype_le_of_countable_eventually_mem_aux`：mk_subtype_le_of
_countable_eventually_mem_aux {α ι : Type u} {a : Cardinal} [Countable ι] {f : ι
 -> Set α} {l : Filter ι} [NeBot l] {t : Set…
· 使用定理 `instCountableULift`：∀ {β : Type v} [Countable β], Countable (ULift.{u, v
} β)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Cardinal.mk_preimage_down`：mk_preimage_down {s : Set α} : #(ULift.down.{
v} ⁻¹' s) = lift.{v} (#s)

--- 原说明 ---
If a set `t` is eventually covered by a countable family of sets, all with cardi
nality at
most `a`, then the cardinality of `t` is also bounded by `a`.
-/
lemma mk_subtype_le_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal}
    [Countable ι] {f : ι → Set α} {l : Filter ι} [NeBot l]
    {t : Set α} (ht : ∀ x ∈ t, ∀ᶠ i in l, x ∈ f i)
    (h'f : ∀ i, #(f i) ≤ a) : #t ≤ a := by
  let g : ULift.{u, v} ι → Set (ULift.{v, u} α) := (ULift.down ⁻¹' ·) ∘ f ∘ ULift.down
  suffices #(ULift.down.{v} ⁻¹' t) ≤ Cardinal.lift.{v, u} a by simpa
  let l' : Filter (ULift.{u} ι) := Filter.map ULift.up l
  apply mk_subtype_le_of_countable_eventually_mem_aux (ι := ULift.{u} ι) (l := l') (f := g)
  · intro x hx
    simpa only [Function.comp_apply, mem_preimage, eventually_map] using! ht _ hx
  · intro i
    simpa [g] using! h'f i.down

/-- If a space is eventually covered by a countable family of sets, all with cardinality at
most `a`, then the cardinality of the space is also bounded by `a`. -/
/-
**Cardinal.mk_le_of_countable_eventually_mem** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal
`。
形式化陈述：mk_le_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal}
 [Countable ι] {f : ι -> Set α} {l : Filter ι} [NeBot l] (ht : forall x, forallᶠ
 i in l, x in f i) (h'f : forall i, #(f i) <= a) : #α <= a
参数：ht : forall x, forallᶠ i in l, x in f i；h'f : forall i, #(f i) <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_univ`：mk_univ {α : Type u} : #(@univ α) = #α
· 使用引理 `Cardinal.mk_subtype_le_of_countable_eventually_mem`：mk_subtype_le_of_cou
ntable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal} [Countable ι] {f 
: ι -> Set α} {l : Filter ι} [NeBot l] {…

--- 原说明 ---
If a space is eventually covered by a countable family of sets, all with cardina
lity at
most `a`, then the cardinality of the space is also bounded by `a`.
-/
lemma mk_le_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal}
    [Countable ι] {f : ι → Set α} {l : Filter ι} [NeBot l] (ht : ∀ x, ∀ᶠ i in l, x ∈ f i)
    (h'f : ∀ i, #(f i) ≤ a) : #α ≤ a := by
  rw [← mk_univ]
  exact mk_subtype_le_of_countable_eventually_mem (l := l) (fun x _ ↦ ht x) h'f

/-- If a space is eventually covered by a countable family of sets, all with cardinality `a`,
then the cardinality of the space is also `a`. -/
/-
**Cardinal.mk_of_countable_eventually_mem** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：mk_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal} [C
ountable ι] {f : ι -> Set α} {l : Filter ι} [NeBot l] (ht : forall x, forallᶠ i 
in l, x in f i) (h'f : forall i, #(f i) = a) : #α = a
参数：ht : forall x, forallᶠ i in l, x in f i；h'f : forall i, #(f i) = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Cardinal.mk_le_of_countable_eventually_mem`：mk_le_of_countable_eventuall
y_mem {α : Type u} {ι : Type v} {a : Cardinal} [Countable ι] {f : ι -> Set α} {l
 : Filter ι} [NeBot l] (ht : for…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Filter.nonempty_of_neBot`：nonempty_of_neBot (f : Filter α) [NeBot f] : N
onempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_set_le`：mk_set_le (s : Set α) : #s <= #α

--- 原说明 ---
If a space is eventually covered by a countable family of sets, all with cardina
lity `a`,
then the cardinality of the space is also `a`.
-/
lemma mk_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal}
    [Countable ι] {f : ι → Set α} {l : Filter ι} [NeBot l] (ht : ∀ x, ∀ᶠ i in l, x ∈ f i)
    (h'f : ∀ i, #(f i) = a) : #α = a := by
  apply le_antisymm
  · apply mk_le_of_countable_eventually_mem ht (fun i ↦ (h'f i).le)
  · obtain ⟨i⟩ : Nonempty ι := nonempty_of_neBot l
    rw [← (h'f i)]
    exact mk_set_le (f i)

end Cardinal

