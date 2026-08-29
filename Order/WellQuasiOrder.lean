/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Aaron Anderson
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Antichain
public import Mathlib.Order.OrderIsoNat

/-!
# Well quasi-orders

A well quasi-order (WQO) is a relation such that any infinite sequence contains an infinite
subsequence of related elements. For a preorder, this is equivalent to having a well-founded order
with no infinite antichains.

## Main definitions

* `WellQuasiOrdered`: a predicate for WQO unbundled relations
* `WellQuasiOrderedLE`: a typeclass for a bundled WQO `≤` relation

## Tags

wqo, pwo, well quasi-order, partial well order, dickson order
-/

@[expose] public section

variable {α β : Type*} {r : α -> α -> Prop} {s : β -> β -> Prop}

/--
Definition of `WellQuasiOrdered` / `WellQuasiOrdered` 的定义

English:
definition WellQuasiOrdered
  signature: (r : α -> α -> Prop)
  body: forall f : Nat -> α, exists m n : Nat, m < n ∧ r (f m) (f n)

中文:
定义 WellQuasiOrdered
  签名: (r : α -> α -> 命题)
  定义体: forall f : Nat -> α, exists m n : Nat, m < n ∧ r (f m) (f n)
-/
def WellQuasiOrdered (r : α -> α -> Prop) : Prop :=
  forall f : Nat -> α, exists m n : Nat, m < n ∧ r (f m) (f n)

/--
theorem `wellQuasiOrdered_of_isEmpty` / 定理 `wellQuasiOrdered_of_isEmpty`

English:
theorem wellQuasiOrdered_of_isEmpty
  given: [IsEmpty α] (r : α -> α -> Prop)
  statement: WellQuasiOrdered r
  proof: fun f => isEmptyElim (f 0)

中文:
定理 wellQuasiOrdered_of_isEmpty
  条件: [是空 α] (r : α -> α -> 命题)
  结论: WellQuasiOrdered r
  证明: fun f => isEmptyElim (f 0)

Depends on / 依赖: isEmptyElim
-/
theorem wellQuasiOrdered_of_isEmpty [IsEmpty α] (r : α -> α -> Prop) : WellQuasiOrdered r :=
  fun f => isEmptyElim (f 0)

/--
theorem `IsAntichain.finite_of_wellQuasiOrdered` / 定理 `IsAntichain.finite_of_wellQuasiOrdered`

English:
theorem IsAntichain.finite_of_wellQuasiOrdered
  statement: {s : Set α} (hs : IsAntichain r s)
  proof: by
  by_contra! hi
  obtain ⟨m, n, hmn, h⟩ := hr fun n => hi.natEmbedding _ n
  exact hmn.ne ((hi.natEmbedding _).injective <| Subtype.val_injective <|
    hs.eq (hi.natEmbedding _ m).2 (hi.natEmbedding _ n).2 h)

中文:
定理 IsAntichain.finite_of_wellQuasiOrdered
  结论: {s : 集合 α} (hs : IsAntichain r s)
  证明: by
  by_contra! hi
  obtain ⟨m, n, hmn, h⟩ := hr fun n => hi.natEmbedding _ n
  exact hmn.ne ((hi.natEmbedding _).injective <| Subtype.val_injective <|
    hs.eq (hi.natEmbedding _ m).2 (hi.natEmbedding _ n).2 h)

Depends on / 依赖: Subtype, Subtype.val_injective, hi.natEmbedding, hmn.ne, hs.eq, injective, natEmbedding, val_injective
-/
theorem IsAntichain.finite_of_wellQuasiOrdered {s : Set α} (hs : IsAntichain r s)
    (hr : WellQuasiOrdered r) : s.Finite := by
  by_contra! hi
  obtain ⟨m, n, hmn, h⟩ := hr fun n => hi.natEmbedding _ n
  exact hmn.ne ((hi.natEmbedding _).injective <| Subtype.val_injective <|
    hs.eq (hi.natEmbedding _ m).2 (hi.natEmbedding _ n).2 h)

/--
theorem `Finite.wellQuasiOrdered` / 定理 `Finite.wellQuasiOrdered`

English:
theorem Finite.wellQuasiOrdered
  given: (r : α -> α -> Prop) [Finite α] [Std.Refl r]
  proof: by
  intro f
  obtain ⟨m, n, h, hf⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem (f := f)
    fun _ => Set.mem_univ _
  exact ⟨m, n, h, hf ▸ refl _⟩

中文:
定理 有限.wellQuasiOrdered
  条件: (r : α -> α -> 命题) [有限 α] [Std.Refl r]
  证明: by
  intro f
  obtain ⟨m, n, h, hf⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem (f := f)
    fun _ => Set.mem_univ _
  exact ⟨m, n, h, hf ▸ refl _⟩

Depends on / 依赖: Set.finite_univ.exists_lt_map_eq_of_forall_mem, Set.mem_univ, exists_lt_map_eq_of_forall_mem, finite_univ, mem_univ
-/
theorem Finite.wellQuasiOrdered (r : α -> α -> Prop) [Finite α] [Std.Refl r] :
    WellQuasiOrdered r := by
  intro f
  obtain ⟨m, n, h, hf⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem (f := f)
    fun _ => Set.mem_univ _
  exact ⟨m, n, h, hf ▸ refl _⟩

/--
theorem `WellQuasiOrdered.exists_monotone_subseq` / 定理 `WellQuasiOrdered.exists_monotone_subseq`

English:
theorem WellQuasiOrdered.exists_monotone_subseq
  statement: [IsPreorder α r] (h : WellQuasiOrdered r)
  proof: by
  obtain ⟨g, h1 | h2⟩ := exists_increasing_or_nonincreasing_subseq r f
  · refine ⟨g, fun m n hle => ?_⟩
    obtain hlt | rfl := hle.lt_or_eq
    exacts [h1 m n hlt, refl_of r _]
  · obtain ⟨m, n, hlt, hle⟩ := h (f ∘ g)
    cases h2 m n hlt hle

中文:
定理 WellQuasiOrdered.存在_monotone_subseq
  结论: [是预序 α r] (h : WellQuasiOrdered r)
  证明: by
  obtain ⟨g, h1 | h2⟩ := exists_increasing_or_nonincreasing_subseq r f
  · refine ⟨g, fun m n hle => ?_⟩
    obtain hlt | rfl := hle.lt_or_eq
    exacts [h1 m n hlt, refl_of r _]
  · obtain ⟨m, n, hlt, hle⟩ := h (f ∘ g)
    cases h2 m n hlt hle

Depends on / 依赖: exacts, exists_increasing_or_nonincreasing_subseq, hle.lt_or_eq, lt_or_eq, refl_of
-/
theorem WellQuasiOrdered.exists_monotone_subseq [IsPreorder α r] (h : WellQuasiOrdered r)
    (f : Nat -> α) : exists g : Nat ↪o Nat, forall m n, m <= n -> r (f (g m)) (f (g n)) := by
  obtain ⟨g, h1 | h2⟩ := exists_increasing_or_nonincreasing_subseq r f
  · refine ⟨g, fun m n hle => ?_⟩
    obtain hlt | rfl := hle.lt_or_eq
    exacts [h1 m n hlt, refl_of r _]
  · obtain ⟨m, n, hlt, hle⟩ := h (f ∘ g)
    cases h2 m n hlt hle

/--
theorem `wellQuasiOrdered_iff_exists_monotone_subseq` / 定理 `wellQuasiOrdered_iff_exists_monotone_subseq`

English:
theorem wellQuasiOrdered_iff_exists_monotone_subseq
  given: [IsPreorder α r]
  proof: by
  constructor <;> intro h f
  · exact h.exists_monotone_subseq f
  · obtain ⟨g, gmon⟩ := h f
    exact ⟨_, _, g.strictMono Nat.zero_lt_one, gmon _ _ (Nat.zero_le 1)⟩

中文:
定理 wellQuasiOrdered_iff_存在_monotone_subseq
  条件: [是预序 α r]
  证明: by
  constructor <;> intro h f
  · exact h.exists_monotone_subseq f
  · obtain ⟨g, gmon⟩ := h f
    exact ⟨_, _, g.strictMono Nat.zero_lt_one, gmon _ _ (Nat.zero_le 1)⟩

Depends on / 依赖: Nat.zero_le, Nat.zero_lt_one, exists_monotone_subseq, g.strictMono, h.exists_monotone_subseq, strictMono, zero_le, zero_lt_one
-/
theorem wellQuasiOrdered_iff_exists_monotone_subseq [IsPreorder α r] :
    WellQuasiOrdered r ↔ forall f : Nat -> α, exists g : Nat ↪o Nat, forall m n : Nat, m <= n -> r (f (g m)) (f (g n)) := by
  constructor <;> intro h f
  · exact h.exists_monotone_subseq f
  · obtain ⟨g, gmon⟩ := h f
    exact ⟨_, _, g.strictMono Nat.zero_lt_one, gmon _ _ (Nat.zero_le 1)⟩

/--
theorem `WellQuasiOrdered.prod` / 定理 `WellQuasiOrdered.prod`

English:
theorem WellQuasiOrdered.prod
  given: [IsPreorder α r] (hr : WellQuasiOrdered r) (hs : WellQuasiOrdered s)
  proof: by
  intro f
  obtain ⟨g, h₁⟩ := hr.exists_monotone_subseq (Prod.fst ∘ f)
  obtain ⟨m, n, h, hf⟩ := hs (Prod.snd ∘ f ∘ g)
  exact ⟨g m, g n, g.strictMono h, h₁ _ _ h.le, hf⟩

中文:
定理 WellQuasiOrdered.乘积
  条件: [是预序 α r] (hr : WellQuasiOrdered r) (hs : WellQuasiOrdered s)
  证明: by
  intro f
  obtain ⟨g, h₁⟩ := hr.exists_monotone_subseq (Prod.fst ∘ f)
  obtain ⟨m, n, h, hf⟩ := hs (Prod.snd ∘ f ∘ g)
  exact ⟨g m, g n, g.strictMono h, h₁ _ _ h.le, hf⟩

Depends on / 依赖: Prod.fst, Prod.snd, exists_monotone_subseq, g.strictMono, h.le, hr.exists_monotone_subseq, strictMono
-/
theorem WellQuasiOrdered.prod [IsPreorder α r] (hr : WellQuasiOrdered r) (hs : WellQuasiOrdered s) :
    WellQuasiOrdered fun a b : α × β => r a.1 b.1 ∧ s a.2 b.2 := by
  intro f
  obtain ⟨g, h₁⟩ := hr.exists_monotone_subseq (Prod.fst ∘ f)
  obtain ⟨m, n, h, hf⟩ := hs (Prod.snd ∘ f ∘ g)
  exact ⟨g m, g n, g.strictMono h, h₁ _ _ h.le, hf⟩

/--
theorem `WellQuasiOrdered.pi` / 定理 `WellQuasiOrdered.pi`

English:
theorem WellQuasiOrdered.pi
  statement: {ι : Type*} {α : ι -> Type*} [Finite ι] {r : forall i, (α i -> α i -> Prop)}
  proof: by
  have := Fintype.ofFinite ι
  have : IsPreorder (forall i, α i) (fun a b : forall i, α i => forall i, r i (a i) (b i)) :=
    { refl a i := refl (a i)
      trans a b c hab hbc i := _root_.trans (hab i) (hbc i) }
  suffices forall (s : Finset ι) (f : Nat -> forall i, α i),
    exists g : Nat ↪o 

中文:
定理 WellQuasiOrdered.pi
  结论: {ι : 类型} {α : ι -> 类型} [有限 ι] {r : 对任意 i, (α i -> α i -> 命题)}
  证明: by
  have := Fintype.ofFinite ι
  have : IsPreorder (forall i, α i) (fun a b : forall i, α i => forall i, r i (a i) (b i)) :=
    { refl a i := refl (a i)
      trans a b c hab hbc i := _root_.trans (hab i) (hbc i) }
  suffices forall (s : Finset ι) (f : Nat -> forall i, α i),
    exists g : Nat ↪o 

Depends on / 依赖: Finset, Finset.mem_univ, Finset.univ, Fintype, Fintype.ofFinite, IsPreorder, _root_, _root_.trans, mem_univ, ofFinite, true_imp_iff, wellQuasiOrdered_iff_exists_monotone_subseq
-/
theorem WellQuasiOrdered.pi {ι : Type*} {α : ι -> Type*} [Finite ι] {r : forall i, (α i -> α i -> Prop)}
    [forall i, IsPreorder (α i) (r i)] (hr : forall i, WellQuasiOrdered (r i)) :
    WellQuasiOrdered fun a b : forall i, α i => forall i, r i (a i) (b i) := by
  have := Fintype.ofFinite ι
  have : IsPreorder (forall i, α i) (fun a b : forall i, α i => forall i, r i (a i) (b i)) :=
    { refl a i := refl (a i)
      trans a b c hab hbc i := _root_.trans (hab i) (hbc i) }
  suffices forall (s : Finset ι) (f : Nat -> forall i, α i),
    exists g : Nat ↪o Nat, forall ⦃a b : Nat⦄, a <= b -> forall i, i in s -> r i ((f ∘ g) a i) ((f ∘ g) b i) by
    rw [wellQuasiOrdered_iff_exists_monotone_subseq]
    intro f
    simpa only [Finset.mem_univ, true_imp_iff] using! this Finset.univ f
  refine Finset.cons_induction ?_ ?_
  · intro f
    exists RelEmbedding.refl (· <= ·)
    simp only [IsEmpty.forall_iff, imp_true_iff, Finset.notMem_empty]
  · intro i s hi ih f
    obtain ⟨g, hg⟩ := (hr i).exists_monotone_subseq (f · i)
    obtain ⟨g', hg'⟩ := ih (f ∘ g)
    refine ⟨g'.trans g, fun a b hab => (Finset.forall_mem_cons _ _).2 ?_⟩
    exact ⟨hg _ _ (OrderHomClass.mono g' hab), hg' hab⟩

/--
theorem `RelIso.wellQuasiOrdered_iff` / 定理 `RelIso.wellQuasiOrdered_iff`

English:
theorem RelIso.wellQuasiOrdered_iff
  given: {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : r ≃r s)
  proof: by
  apply (Equiv.arrowCongr (.refl Nat) f).forall_congr
  congr! with g a b
  simp [f.map_rel_iff]

中文:
定理 RelIso.wellQuasiOrdered_iff
  条件: {α β} {r : α -> α -> 命题} {s : β -> β -> 命题} (f : r ≃r s)
  证明: by
  apply (Equiv.arrowCongr (.refl Nat) f).forall_congr
  congr! with g a b
  simp [f.map_rel_iff]

Depends on / 依赖: Equiv.arrowCongr, arrowCongr, f.map_rel_iff, forall_congr, map_rel_iff
-/
theorem RelIso.wellQuasiOrdered_iff {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : r ≃r s) :
    WellQuasiOrdered r ↔ WellQuasiOrdered s := by
  apply (Equiv.arrowCongr (.refl Nat) f).forall_congr
  congr! with g a b
  simp [f.map_rel_iff]

/--
theorem `WellQuasiOrdered.of_surjective` / 定理 `WellQuasiOrdered.of_surjective`

English:
theorem WellQuasiOrdered.of_surjective
  statement: {α β} {r : α -> α -> Prop}
  proof: by
  intro seq
  have ⟨_, _, hle, hr⟩ := h (Function.surjInv hf ∘ seq)
  exact ⟨_, _, hle, by simpa [Function.surjInv_eq] using f.map_rel hr⟩

中文:
定理 WellQuasiOrdered.of_surjective
  结论: {α β} {r : α -> α -> 命题}
  证明: by
  intro seq
  have ⟨_, _, hle, hr⟩ := h (Function.surjInv hf ∘ seq)
  exact ⟨_, _, hle, by simpa [Function.surjInv_eq] using f.map_rel hr⟩

Depends on / 依赖: Function, Function.surjInv, Function.surjInv_eq, f.map_rel, map_rel, surjInv, surjInv_eq
-/
theorem WellQuasiOrdered.of_surjective {α β} {r : α -> α -> Prop}
    {s : β -> β -> Prop} (h : WellQuasiOrdered r) (f : r ->r s) (hf : Function.Surjective f) :
    WellQuasiOrdered s := by
  intro seq
  have ⟨_, _, hle, hr⟩ := h (Function.surjInv hf ∘ seq)
  exact ⟨_, _, hle, by simpa [Function.surjInv_eq] using f.map_rel hr⟩

/-- A typeclass for an order with a well-quasi-ordered `≤` relation.

Note that this is unlike `WellFoundedLT`, which instead takes a `<` relation. -/
@[mk_iff wellQuasiOrderedLE_def]
/--
Definition of `WellQuasiOrderedLE` / `WellQuasiOrderedLE` 的定义

English:
class WellQuasiOrderedLE
  parameters: (α : Type*) [LE α]
  axioms and operations (1):
    - wqo : @WellQuasiOrdered α (· <= ·)

中文:
类 良拟序
  参数: (α : 类型) [LE α]
  公理与运算 (1 个):
    - wqo : @WellQuasiOrdered α (· <= ·)
-/
class WellQuasiOrderedLE (α : Type*) [LE α] where
  wqo : @WellQuasiOrdered α (· <= ·)

/--
theorem `wellQuasiOrdered_le` / 定理 `wellQuasiOrdered_le`

English:
theorem wellQuasiOrdered_le
  given: [LE α] [h : WellQuasiOrderedLE α]
  statement: @WellQuasiOrdered α (· <= ·)
  proof: h.wqo

中文:
定理 wellQuasiOrdered_le
  条件: [LE α] [h : 良拟序 α]
  结论: @WellQuasiOrdered α (· <= ·)
  证明: h.wqo

Depends on / 依赖: h.wqo
-/
theorem wellQuasiOrdered_le [LE α] [h : WellQuasiOrderedLE α] : @WellQuasiOrdered α (· <= ·) :=
  h.wqo

/--
theorem `OrderIso.wellQuasiOrderedLE_iff` / 定理 `OrderIso.wellQuasiOrderedLE_iff`

English:
theorem OrderIso.wellQuasiOrderedLE_iff
  given: {α β} [LE α] [LE β] (f : α ≃o β)
  proof: by
  simpa [wellQuasiOrderedLE_def] using f.wellQuasiOrdered_iff

中文:
定理 OrderIso.wellQuasiOrderedLE_iff
  条件: {α β} [LE α] [LE β] (f : α ≃o β)
  证明: by
  simpa [wellQuasiOrderedLE_def] using f.wellQuasiOrdered_iff

Depends on / 依赖: f.wellQuasiOrdered_iff, wellQuasiOrderedLE_def, wellQuasiOrdered_iff
-/
theorem OrderIso.wellQuasiOrderedLE_iff {α β} [LE α] [LE β] (f : α ≃o β) :
    WellQuasiOrderedLE α ↔ WellQuasiOrderedLE β := by
  simpa [wellQuasiOrderedLE_def] using f.wellQuasiOrdered_iff

section Preorder
variable [Preorder α]

-- This was previously a global instance,
-- but it doesn't appear to be used and has been implicated in slow typeclass resolutions.
/--
lemma `Finite.to_wellQuasiOrderedLE` / 引理 `Finite.to_wellQuasiOrderedLE`

English:
lemma Finite.to_wellQuasiOrderedLE
  given: [Finite α]
  statement: WellQuasiOrderedLE α where
  proof: Finite.wellQuasiOrdered _

中文:
引理 有限.to_wellQuasiOrderedLE
  条件: [有限 α]
  结论: 良拟序 α where
  证明: Finite.wellQuasiOrdered _

Depends on / 依赖: Finite, Finite.wellQuasiOrdered, wellQuasiOrdered
-/
lemma Finite.to_wellQuasiOrderedLE [Finite α] : WellQuasiOrderedLE α where
  wqo := Finite.wellQuasiOrdered _

instance (priority := 100) WellQuasiOrderedLE.to_wellFoundedLT [WellQuasiOrderedLE α] :
    WellFoundedLT α := by
  rw [WellFoundedLT]; rw [isWellFounded_iff]; rw [RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun f => ?_⟩
  obtain ⟨a, b, h, hf⟩ := wellQuasiOrdered_le f
  exact (f.map_rel_iff.2 h).not_ge hf

/--
theorem `WellQuasiOrdered.wellFounded` / 定理 `WellQuasiOrdered.wellFounded`

English:
theorem WellQuasiOrdered.wellFounded
  statement: {α : Type*} {r : α -> α -> Prop} [IsPreorder α r]
  proof: by
  let _ : Preorder α :=
    { le := r
      le_refl := refl_of r
      le_trans := fun _ _ _ => trans_of r }
  have : WellQuasiOrderedLE α := ⟨h⟩
  exact wellFounded_lt

中文:
定理 WellQuasiOrdered.wellFounded
  结论: {α : 类型} {r : α -> α -> 命题} [是预序 α r]
  证明: by
  let _ : Preorder α :=
    { le := r
      le_refl := refl_of r
      le_trans := fun _ _ _ => trans_of r }
  have : WellQuasiOrderedLE α := ⟨h⟩
  exact wellFounded_lt

Depends on / 依赖: Preorder, WellQuasiOrderedLE, le_refl, le_trans, refl_of, trans_of, wellFounded_lt
-/
theorem WellQuasiOrdered.wellFounded {α : Type*} {r : α -> α -> Prop} [IsPreorder α r]
    (h : WellQuasiOrdered r) : WellFounded fun a b => r a b ∧ ¬ r b a := by
  let _ : Preorder α :=
    { le := r
      le_refl := refl_of r
      le_trans := fun _ _ _ => trans_of r }
  have : WellQuasiOrderedLE α := ⟨h⟩
  exact wellFounded_lt

/--
theorem `WellQuasiOrderedLE.finite_of_isAntichain` / 定理 `WellQuasiOrderedLE.finite_of_isAntichain`

English:
theorem WellQuasiOrderedLE.finite_of_isAntichain
  statement: [WellQuasiOrderedLE α] {s : Set α}
  proof: h.finite_of_wellQuasiOrdered wellQuasiOrdered_le

中文:
定理 良拟序.finite_of_isAntichain
  结论: [良拟序 α] {s : 集合 α}
  证明: h.finite_of_wellQuasiOrdered wellQuasiOrdered_le

Depends on / 依赖: finite_of_wellQuasiOrdered, h.finite_of_wellQuasiOrdered, wellQuasiOrdered_le
-/
theorem WellQuasiOrderedLE.finite_of_isAntichain [WellQuasiOrderedLE α] {s : Set α}
    (h : IsAntichain (· <= ·) s) : s.Finite :=
  h.finite_of_wellQuasiOrdered wellQuasiOrdered_le

/--
theorem `wellQuasiOrderedLE_iff` / 定理 `wellQuasiOrderedLE_iff`

English:
theorem wellQuasiOrderedLE_iff
  proof: by
  refine ⟨fun h => ⟨h.to_wellFoundedLT, fun s => h.finite_of_isAntichain⟩,
    fun ⟨hwf, hc⟩ => ⟨fun f => ?_⟩⟩
  obtain ⟨g, h1 | h2⟩ := exists_increasing_or_nonincreasing_subseq (· > ·) f
  · exfalso
    apply RelEmbedding.not_wellFounded _ hwf.wf
    exact (RelEmbedding.ofMonotone _ h1).swap
  ·

中文:
定理 wellQuasiOrderedLE_iff
  证明: by
  refine ⟨fun h => ⟨h.to_wellFoundedLT, fun s => h.finite_of_isAntichain⟩,
    fun ⟨hwf, hc⟩ => ⟨fun f => ?_⟩⟩
  obtain ⟨g, h1 | h2⟩ := exists_increasing_or_nonincreasing_subseq (· > ·) f
  · exfalso
    apply RelEmbedding.not_wellFounded _ hwf.wf
    exact (RelEmbedding.ofMonotone _ h1).swap
  ·

Depends on / 依赖: RelEmbedding, RelEmbedding.not_wellFounded, RelEmbedding.ofMonotone, Set.range, contrapose, exists_increasing_or_nonincreasing_subseq, finite_of_isAntichain, g.strictMono, h.finite_of_isAntichain, h.to_wellFoundedLT, hwf.wf, lt_of_le_not_ge, lt_trichotomy, not_wellFounded, ofMonotone, strictMono, to_wellFoundedLT
-/
theorem wellQuasiOrderedLE_iff :
    WellQuasiOrderedLE α ↔ WellFoundedLT α ∧ forall s : Set α, IsAntichain (· <= ·) s -> s.Finite := by
  refine ⟨fun h => ⟨h.to_wellFoundedLT, fun s => h.finite_of_isAntichain⟩,
    fun ⟨hwf, hc⟩ => ⟨fun f => ?_⟩⟩
  obtain ⟨g, h1 | h2⟩ := exists_increasing_or_nonincreasing_subseq (· > ·) f
  · exfalso
    apply RelEmbedding.not_wellFounded _ hwf.wf
    exact (RelEmbedding.ofMonotone _ h1).swap
  · contrapose! hc
    refine ⟨Set.range (f ∘ g), ?_, ?_⟩
    · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ _ hf
      obtain h | rfl | h := lt_trichotomy m n
      · exact hc _ _ (g.strictMono h) hf
      · contradiction
      · exact h2 _ _ h (lt_of_le_not_ge hf (hc _ _ (g.strictMono h)))
    · refine Set.infinite_range_of_injective fun m n (hf : f (g m) = f (g n)) => ?_
      obtain h | rfl | h := lt_trichotomy m n <;>
        (first | rfl | cases (hf ▸ hc _ _ (g.strictMono h)) le_rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [WellQuasiOrderedLE
  signature: α] [Preorder β] [WellQuasiOrderedLE β] : WellQuasiOrderedLE (α × β)
  body: ⟨wellQuasiOrdered_le.prod wellQuasiOrdered_le⟩

中文:
实例 [良拟序
  签名: α] [预序 β] [良拟序 β] : 良拟序 (α × β)
  定义体: ⟨wellQuasiOrdered_le.prod wellQuasiOrdered_le⟩

Depends on / 依赖: IsReduced, IsReduced.eq_zero, congr_fun, eq_zero, wellQuasiOrdered_le, wellQuasiOrdered_le.prod
-/
instance [WellQuasiOrderedLE α] [Preorder β] [WellQuasiOrderedLE β] : WellQuasiOrderedLE (α × β) :=
  ⟨wellQuasiOrdered_le.prod wellQuasiOrdered_le⟩

/--
theorem `Monotone.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective` / 定理 `Monotone.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective`

English:
theorem Monotone.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective
  statement: [Preorder β]
  proof: ⟨wellQuasiOrdered_le.of_surjective ⟨_, (mono ·)⟩ hf⟩

中文:
定理 递增.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective
  结论: [预序 β]
  证明: ⟨wellQuasiOrdered_le.of_surjective ⟨_, (mono ·)⟩ hf⟩

Depends on / 依赖: of_surjective, wellQuasiOrdered_le, wellQuasiOrdered_le.of_surjective
-/
theorem Monotone.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective [Preorder β]
    [WellQuasiOrderedLE α] {f : α -> β} (mono : Monotone f) (hf : Function.Surjective f) :
    WellQuasiOrderedLE β :=
  ⟨wellQuasiOrdered_le.of_surjective ⟨_, (mono ·)⟩ hf⟩

/--
theorem `OrderHom.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective` / 定理 `OrderHom.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective`

English:
theorem OrderHom.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective
  statement: [Preorder β]
  proof: f.monotone.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective hf

中文:
定理 序态射.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective
  结论: [预序 β]
  证明: f.monotone.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective hf

Depends on / 依赖: f.monotone.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective, monotone, wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective
-/
theorem OrderHom.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective [Preorder β]
    [WellQuasiOrderedLE α] (f : α ->o β) (hf : Function.Surjective f) :
    WellQuasiOrderedLE β :=
  f.monotone.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective hf

end Preorder

section LinearOrder
variable [LinearOrder α]

/--
theorem `wellQuasiOrderedLE_iff_wellFoundedLT` / 定理 `wellQuasiOrderedLE_iff_wellFoundedLT`

English:
theorem wellQuasiOrderedLE_iff_wellFoundedLT
  statement: WellQuasiOrderedLE α ↔ WellFoundedLT α
  proof: by
  rw [wellQuasiOrderedLE_iff]; rw [and_iff_left_iff_imp]
  exact fun _ s hs => hs.subsingleton.finite

中文:
定理 wellQuasiOrderedLE_iff_wellFoundedLT
  结论: 良拟序 α ↔ WellFoundedLT α
  证明: by
  rw [wellQuasiOrderedLE_iff]; rw [and_iff_left_iff_imp]
  exact fun _ s hs => hs.subsingleton.finite

Depends on / 依赖: and_iff_left_iff_imp, finite, hs.subsingleton.finite, subsingleton, wellQuasiOrderedLE_iff
-/
theorem wellQuasiOrderedLE_iff_wellFoundedLT : WellQuasiOrderedLE α ↔ WellFoundedLT α := by
  rw [wellQuasiOrderedLE_iff]; rw [and_iff_left_iff_imp]
  exact fun _ s hs => hs.subsingleton.finite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : WellFoundedLT α] : WellQuasiOrderedLE α
  body: wellQuasiOrderedLE_iff_wellFoundedLT.mpr h

中文:
实例 [h
  签名: : WellFoundedLT α] : 良拟序 α
  定义体: wellQuasiOrderedLE_iff_wellFoundedLT.mpr h

Depends on / 依赖: wellQuasiOrderedLE_iff_wellFoundedLT, wellQuasiOrderedLE_iff_wellFoundedLT.mpr
-/
instance [h : WellFoundedLT α] : WellQuasiOrderedLE α :=
  wellQuasiOrderedLE_iff_wellFoundedLT.mpr h

end LinearOrder

/--
Instance `Pi.wellQuasiOrderedLE` / 实例 `Pi.wellQuasiOrderedLE`

English:
instance Pi.wellQuasiOrderedLE
  signature: {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α i)]
  body: ⟨WellQuasiOrdered.pi fun i => (h i).wqo⟩

中文:
实例 依赖函数类型.wellQuasiOrderedLE
  签名: {ι : 类型} {α : ι -> 类型} [对任意 i, 预序 (α i)]
  定义体: ⟨WellQuasiOrdered.pi fun i => (h i).wqo⟩

Depends on / 依赖: WellQuasiOrdered, WellQuasiOrdered.pi
-/
instance Pi.wellQuasiOrderedLE {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α i)]
    [h : forall i, WellQuasiOrderedLE (α i)] [Finite ι] : WellQuasiOrderedLE (forall i, α i) :=
  ⟨WellQuasiOrdered.pi fun i => (h i).wqo⟩
