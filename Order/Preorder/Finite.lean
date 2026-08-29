/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.Minimal

/-!
# Finite preorders and finite sets in a preorder

This file shows that non-empty finite sets in a preorder have minimal/maximal elements, and
contrapositively that non-empty sets without minimal or maximal elements are infinite.

It also provides uniqueness results for order embeddings and order homomorphisms on finite linear
orders.
-/

public section

variable {ι α β : Type*}

namespace Finset
section IsTrans
variable [LE α] [IsTrans α LE.le] {s : Finset α} {a : α}

@[to_dual]
/--
lemma `exists_maximalFor` / 引理 `exists_maximalFor`

English:
lemma exists_maximalFor
  given: (f : ι -> α) (s : Finset ι) (hs : s.Nonempty)
  proof: by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => exact ⟨i, by simp⟩
  | @cons i s hi hs ih =>
    obtain ⟨j, hj⟩ := ih
    by_cases hji : f j <= f i
    · refine ⟨i, mem_cons_self .., ?_⟩
      simp only [mem_cons, forall_eq_or_imp, imp_self, true_and]
      exact fun k

中文:
引理 存在_maximalFor
  条件: (f : ι -> α) (s : 有限集 ι) (hs : s.非空)
  证明: by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => exact ⟨i, by simp⟩
  | @cons i s hi hs ih =>
    obtain ⟨j, hj⟩ := ih
    by_cases hji : f j <= f i
    · refine ⟨i, mem_cons_self .., ?_⟩
      simp only [mem_cons, forall_eq_or_imp, imp_self, true_and]
      exact fun k

Depends on / 依赖: Finset, Finset.Nonempty.cons_induction, Nonempty, _root_, _root_.trans, cons_induction, forall_eq_or_imp, imp_self, mem_cons, mem_cons_of_mem, mem_cons_self, singleton, true_and
-/
lemma exists_maximalFor (f : ι -> α) (s : Finset ι) (hs : s.Nonempty) :
    exists i, MaximalFor (· in s) f i := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => exact ⟨i, by simp⟩
  | @cons i s hi hs ih =>
    obtain ⟨j, hj⟩ := ih
    by_cases hji : f j <= f i
    · refine ⟨i, mem_cons_self .., ?_⟩
      simp only [mem_cons, forall_eq_or_imp, imp_self, true_and]
      exact fun k hk hik => _root_.trans (hj.2 hk <| _root_.trans hji hik) hji
    · exact ⟨j, mem_cons_of_mem hj.1, by simpa [hji] using hj.2⟩

@[to_dual]
/--
lemma `exists_maximal` / 引理 `exists_maximal`

English:
lemma exists_maximal
  given: (hs : s.Nonempty)
  statement: exists i, Maximal (· in s) i
  proof: s.exists_maximalFor id hs

中文:
引理 存在_maximal
  条件: (hs : s.非空)
  结论: 存在 i, 极大 (· in s) i
  证明: s.exists_maximalFor id hs

Depends on / 依赖: exists_maximalFor, s.exists_maximalFor
-/
lemma exists_maximal (hs : s.Nonempty) : exists i, Maximal (· in s) i := s.exists_maximalFor id hs

end IsTrans

section Preorder
variable [Preorder α] {s : Finset α} {a : α}

@[to_dual]
/--
lemma `exists_le_maximal` / 引理 `exists_le_maximal`

English:
lemma exists_le_maximal
  given: (s : Finset α) (ha : a in s)
  statement: exists b, a <= b ∧ Maximal (· in s) b
  proof: by
  classical
  obtain ⟨b, hb, hab, hbmin⟩ : exists b in s, a <= b ∧ _ := by
    simpa [Maximal, and_assoc] using {x in s | a <= x}.exists_maximal ⟨a, mem_filter.2 ⟨ha, le_rfl⟩⟩
  exact ⟨b, hab, hb, fun c hc hbc => hbmin hc (hab.trans hbc) hbc⟩

中文:
引理 存在_le_maximal
  条件: (s : 有限集 α) (ha : a in s)
  结论: 存在 b, a <= b ∧ 极大 (· in s) b
  证明: by
  classical
  obtain ⟨b, hb, hab, hbmin⟩ : exists b in s, a <= b ∧ _ := by
    simpa [Maximal, and_assoc] using {x in s | a <= x}.exists_maximal ⟨a, mem_filter.2 ⟨ha, le_rfl⟩⟩
  exact ⟨b, hab, hb, fun c hc hbc => hbmin hc (hab.trans hbc) hbc⟩

Depends on / 依赖: Maximal, and_assoc, classical, exists_maximal, hab.trans, le_rfl, mem_filter
-/
lemma exists_le_maximal (s : Finset α) (ha : a in s) : exists b, a <= b ∧ Maximal (· in s) b := by
  classical
  obtain ⟨b, hb, hab, hbmin⟩ : exists b in s, a <= b ∧ _ := by
    simpa [Maximal, and_assoc] using {x in s | a <= x}.exists_maximal ⟨a, mem_filter.2 ⟨ha, le_rfl⟩⟩
  exact ⟨b, hab, hb, fun c hc hbc => hbmin hc (hab.trans hbc) hbc⟩

end Preorder
end Finset

namespace Set
section IsTrans
variable [LE α] [IsTrans α LE.le] {s : Set α} {a : α}

@[to_dual]
/--
lemma `Finite.exists_maximalFor` / 引理 `Finite.exists_maximalFor`

English:
lemma Finite.exists_maximalFor
  given: (f : ι -> α) (s : Set ι) (h : s.Finite) (hs : s.Nonempty)
  proof: by
  lift s to Finset ι using h; exact s.exists_maximalFor f hs

@[to_dual]

中文:
引理 有限.存在_maximalFor
  条件: (f : ι -> α) (s : 集合 ι) (h : s.有限) (hs : s.非空)
  证明: by
  lift s to Finset ι using h; exact s.exists_maximalFor f hs

@[to_dual]

Depends on / 依赖: Finset, exists_maximalFor, s.exists_maximalFor
-/
lemma Finite.exists_maximalFor (f : ι -> α) (s : Set ι) (h : s.Finite) (hs : s.Nonempty) :
    exists i, MaximalFor (· in s) f i := by
  lift s to Finset ι using h; exact s.exists_maximalFor f hs

@[to_dual]
/--
lemma `Finite.exists_maximal` / 引理 `Finite.exists_maximal`

English:
lemma Finite.exists_maximal
  given: (h : s.Finite) (hs : s.Nonempty)
  statement: exists i, Maximal (· in s) i
  proof: h.exists_maximalFor id _ hs

中文:
引理 有限.存在_maximal
  条件: (h : s.有限) (hs : s.非空)
  结论: 存在 i, 极大 (· in s) i
  证明: h.exists_maximalFor id _ hs

Depends on / 依赖: exists_maximalFor, h.exists_maximalFor
-/
lemma Finite.exists_maximal (h : s.Finite) (hs : s.Nonempty) : exists i, Maximal (· in s) i :=
  h.exists_maximalFor id _ hs

/-- A version of `Finite.exists_maximalFor` with the (weaker) hypothesis that the image of `s`
is finite rather than `s` itself. -/
@[to_dual /- A version of `Finite.exists_minimalFor` with the (weaker) hypothesis that the image of
`s` is finite rather than `s` itself.-/]
/--
lemma `Finite.exists_maximalFor'` / 引理 `Finite.exists_maximalFor'`

English:
lemma Finite.exists_maximalFor'
  given: (f : ι -> α) (s : Set ι) (h : (f '' s).Finite) (hs : s.Nonempty)
  proof: by
  obtain ⟨_, ⟨a, ha, rfl⟩, hmax⟩ := Finite.exists_maximalFor id (f '' s) h (hs.image f)
  exact ⟨a, ha, fun a' ha' hf => hmax (mem_image_of_mem f ha') hf⟩

中文:
引理 有限.存在_maximalFor'
  条件: (f : ι -> α) (s : 集合 ι) (h : (f '' s).有限) (hs : s.非空)
  证明: by
  obtain ⟨_, ⟨a, ha, rfl⟩, hmax⟩ := Finite.exists_maximalFor id (f '' s) h (hs.image f)
  exact ⟨a, ha, fun a' ha' hf => hmax (mem_image_of_mem f ha') hf⟩

Depends on / 依赖: Finite, Finite.exists_maximalFor, exists_maximalFor, hs.image, mem_image_of_mem
-/
lemma Finite.exists_maximalFor' (f : ι -> α) (s : Set ι) (h : (f '' s).Finite) (hs : s.Nonempty) :
    exists i, MaximalFor (· in s) f i := by
  obtain ⟨_, ⟨a, ha, rfl⟩, hmax⟩ := Finite.exists_maximalFor id (f '' s) h (hs.image f)
  exact ⟨a, ha, fun a' ha' hf => hmax (mem_image_of_mem f ha') hf⟩

end IsTrans

section Preorder
variable [Preorder α] {s : Set α} {a : α}

@[to_dual]
/--
lemma `Finite.exists_le_maximal` / 引理 `Finite.exists_le_maximal`

English:
lemma Finite.exists_le_maximal
  given: (hs : s.Finite) (ha : a in s)
  statement: exists b, a <= b ∧ Maximal (· in s) b
  proof: by
  lift s to Finset α using hs; exact s.exists_le_maximal ha

中文:
引理 有限.存在_le_maximal
  条件: (hs : s.有限) (ha : a in s)
  结论: 存在 b, a <= b ∧ 极大 (· in s) b
  证明: by
  lift s to Finset α using hs; exact s.exists_le_maximal ha

Depends on / 依赖: Finset, exists_le_maximal, s.exists_le_maximal
-/
lemma Finite.exists_le_maximal (hs : s.Finite) (ha : a in s) : exists b, a <= b ∧ Maximal (· in s) b := by
  lift s to Finset α using hs; exact s.exists_le_maximal ha

variable [Nonempty α]

/--
lemma `infinite_of_forall_exists_gt` / 引理 `infinite_of_forall_exists_gt`

English:
lemma infinite_of_forall_exists_gt
  given: (h : forall a, exists b in s, a < b)
  statement: s.Infinite
  proof: by
  inhabit α
  let f (n : Nat) : α := Nat.recOn n (h default).choose fun _ a => (h a).choose
  have hf : forall n, f n in s := by rintro (_ | _) <;> exact (h _).choose_spec.1
  exact infinite_of_injective_forall_mem
    (strictMono_nat_of_lt_succ fun n => (h _).choose_spec.2).injective hf

@[to_du

中文:
引理 infinite_of_对任意_存在_gt
  条件: (h : 对任意 a, 存在 b in s, a < b)
  结论: s.无限
  证明: by
  inhabit α
  let f (n : Nat) : α := Nat.recOn n (h default).choose fun _ a => (h a).choose
  have hf : forall n, f n in s := by rintro (_ | _) <;> exact (h _).choose_spec.1
  exact infinite_of_injective_forall_mem
    (strictMono_nat_of_lt_succ fun n => (h _).choose_spec.2).injective hf

@[to_du

Depends on / 依赖: Nat.recOn, choose_spec, infinite_of_injective_forall_mem, inhabit, injective, strictMono_nat_of_lt_succ
-/
lemma infinite_of_forall_exists_gt (h : forall a, exists b in s, a < b) : s.Infinite := by
  inhabit α
  let f (n : Nat) : α := Nat.recOn n (h default).choose fun _ a => (h a).choose
  have hf : forall n, f n in s := by rintro (_ | _) <;> exact (h _).choose_spec.1
  exact infinite_of_injective_forall_mem
    (strictMono_nat_of_lt_succ fun n => (h _).choose_spec.2).injective hf

@[to_dual existing infinite_of_forall_exists_gt]
/--
lemma `infinite_of_forall_exists_lt` / 引理 `infinite_of_forall_exists_lt`

English:
lemma infinite_of_forall_exists_lt
  given: (h : forall a, exists b in s, b < a)
  statement: s.Infinite
  proof: infinite_of_forall_exists_gt (α := αᵒᵈ) h

中文:
引理 infinite_of_对任意_存在_lt
  条件: (h : 对任意 a, 存在 b in s, b < a)
  结论: s.无限
  证明: infinite_of_forall_exists_gt (α := αᵒᵈ) h

Depends on / 依赖: infinite_of_forall_exists_gt
-/
lemma infinite_of_forall_exists_lt (h : forall a, exists b in s, b < a) : s.Infinite :=
  infinite_of_forall_exists_gt (α := αᵒᵈ) h

end Preorder

section PartialOrder
variable (α) [PartialOrder α]

@[to_dual]
/--
lemma `finite_isTop` / 引理 `finite_isTop`

English:
lemma finite_isTop
  statement: {a : α | IsTop a}.Finite
  proof: (subsingleton_isTop α).finite

中文:
引理 finite_isTop
  结论: {a : α | IsTop a}.有限
  证明: (subsingleton_isTop α).finite

Depends on / 依赖: finite, subsingleton_isTop
-/
lemma finite_isTop : {a : α | IsTop a}.Finite := (subsingleton_isTop α).finite

end PartialOrder

section LinearOrder
variable [LinearOrder α] {s : Set α} {t : Set β} {f : α -> β}

/--
lemma `Infinite.exists_lt_map_eq_of_mapsTo` / 引理 `Infinite.exists_lt_map_eq_of_mapsTo`

English:
lemma Infinite.exists_lt_map_eq_of_mapsTo
  given: (hs : s.Infinite) (hf : MapsTo f s t) (ht : t.Finite)
  proof: let ⟨x, hx, y, hy, hxy, hf⟩ := hs.exists_ne_map_eq_of_mapsTo hf ht
  hxy.lt_or_gt.elim (fun hxy => ⟨x, hx, y, hy, hxy, hf⟩) fun hyx => ⟨y, hy, x, hx, hyx, hf.symm⟩

中文:
引理 无限.存在_lt_map_eq_of_mapsTo
  条件: (hs : s.无限) (hf : 映射到 f s t) (ht : t.有限)
  证明: let ⟨x, hx, y, hy, hxy, hf⟩ := hs.exists_ne_map_eq_of_mapsTo hf ht
  hxy.lt_or_gt.elim (fun hxy => ⟨x, hx, y, hy, hxy, hf⟩) fun hyx => ⟨y, hy, x, hx, hyx, hf.symm⟩

Depends on / 依赖: exists_ne_map_eq_of_mapsTo, hf.symm, hs.exists_ne_map_eq_of_mapsTo, hxy.lt_or_gt.elim, lt_or_gt
-/
lemma Infinite.exists_lt_map_eq_of_mapsTo (hs : s.Infinite) (hf : MapsTo f s t) (ht : t.Finite) :
    exists x in s, exists y in s, x < y ∧ f x = f y :=
  let ⟨x, hx, y, hy, hxy, hf⟩ := hs.exists_ne_map_eq_of_mapsTo hf ht
  hxy.lt_or_gt.elim (fun hxy => ⟨x, hx, y, hy, hxy, hf⟩) fun hyx => ⟨y, hy, x, hx, hyx, hf.symm⟩

/--
lemma `Finite.exists_lt_map_eq_of_forall_mem` / 引理 `Finite.exists_lt_map_eq_of_forall_mem`

English:
lemma Finite.exists_lt_map_eq_of_forall_mem
  given: [Infinite α] (hf : forall a, f a in t) (ht : t.Finite)
  proof: by
  rw [← mapsTo_univ_iff] at hf
  obtain ⟨a, -, b, -, h⟩ := infinite_univ.exists_lt_map_eq_of_mapsTo hf ht
  exact ⟨a, b, h⟩

中文:
引理 有限.存在_lt_map_eq_of_对任意_mem
  条件: [无限 α] (hf : 对任意 a, f a in t) (ht : t.有限)
  证明: by
  rw [← mapsTo_univ_iff] at hf
  obtain ⟨a, -, b, -, h⟩ := infinite_univ.exists_lt_map_eq_of_mapsTo hf ht
  exact ⟨a, b, h⟩

Depends on / 依赖: exists_lt_map_eq_of_mapsTo, infinite_univ, infinite_univ.exists_lt_map_eq_of_mapsTo, mapsTo_univ_iff
-/
lemma Finite.exists_lt_map_eq_of_forall_mem [Infinite α] (hf : forall a, f a in t) (ht : t.Finite) :
    exists a b, a < b ∧ f a = f b := by
  rw [← mapsTo_univ_iff] at hf
  obtain ⟨a, -, b, -, h⟩ := infinite_univ.exists_lt_map_eq_of_mapsTo hf ht
  exact ⟨a, b, h⟩

/--
theorem `Finite.exists_subsingleton_isCofinal` / 定理 `Finite.exists_subsingleton_isCofinal`

English:
theorem Finite.exists_subsingleton_isCofinal
  given: {s : Set α} (hs : s.Finite) (hs' : IsCofinal s)
  proof: by
  obtain rfl | hn := s.eq_empty_or_nonempty
  · use ∅; simpa
  · obtain ⟨a, ha⟩ := hs.exists_maximal hn
    use {a}
    suffices IsTop a by simpa [IsCofinal]
    intro b
    obtain ⟨c, hc, hbc⟩ := hs' b
    exact hbc.trans (ha.le hc)

中文:
定理 有限.存在_subsingleton_isCofinal
  条件: {s : 集合 α} (hs : s.有限) (hs' : IsCofinal s)
  证明: by
  obtain rfl | hn := s.eq_empty_or_nonempty
  · use ∅; simpa
  · obtain ⟨a, ha⟩ := hs.exists_maximal hn
    use {a}
    suffices IsTop a by simpa [IsCofinal]
    intro b
    obtain ⟨c, hc, hbc⟩ := hs' b
    exact hbc.trans (ha.le hc)

Depends on / 依赖: IsCofinal, eq_empty_or_nonempty, exists_maximal, ha.le, hbc.trans, hs.exists_maximal, s.eq_empty_or_nonempty
-/
theorem Finite.exists_subsingleton_isCofinal {s : Set α} (hs : s.Finite) (hs' : IsCofinal s) :
    exists t : Set α, t.Subsingleton ∧ IsCofinal t := by
  obtain rfl | hn := s.eq_empty_or_nonempty
  · use ∅; simpa
  · obtain ⟨a, ha⟩ := hs.exists_maximal hn
    use {a}
    suffices IsTop a by simpa [IsCofinal]
    intro b
    obtain ⟨c, hc, hbc⟩ := hs' b
    exact hbc.trans (ha.le hc)

end LinearOrder
end Set

section Preorder
variable [Preorder α] [Finite α] {p : α -> Prop} {a : α}

@[to_dual]
/--
lemma `Finite.exists_le_maximal` / 引理 `Finite.exists_le_maximal`

English:
lemma Finite.exists_le_maximal
  given: (h : p a)
  statement: exists b, a <= b ∧ Maximal p b
  proof: {x | p x}.toFinite.exists_le_maximal h

中文:
引理 有限.存在_le_maximal
  条件: (h : p a)
  结论: 存在 b, a <= b ∧ 极大 p b
  证明: {x | p x}.toFinite.exists_le_maximal h
-/
lemma Finite.exists_le_maximal (h : p a) : exists b, a <= b ∧ Maximal p b :=
  {x | p x}.toFinite.exists_le_maximal h

end Preorder

@[elab_as_elim, deprecated "Use `WellFoundedLT.induction _ h` instead." (since := "2026-04-10")]
/--
lemma `LinearOrder.strong_induction_of_finite` / 引理 `LinearOrder.strong_induction_of_finite`

English:
lemma LinearOrder.strong_induction_of_finite
  proof: WellFoundedLT.induction _ h

中文:
引理 线性序.strong_induction_of_finite
  证明: WellFoundedLT.induction _ h

Depends on / 依赖: WellFoundedLT, WellFoundedLT.induction
-/
lemma LinearOrder.strong_induction_of_finite
    {α : Type*} [LinearOrder α] [Finite α] {motive : α -> Prop}
    (h : forall (j : α) (_ : forall (k : α), k < j -> motive k), motive j) (i : α) :
    motive i := WellFoundedLT.induction _ h

/--
lemma `OrderEmbedding.range_eq_iff` / 引理 `OrderEmbedding.range_eq_iff`

English:
lemma OrderEmbedding.range_eq_iff
  proof: by
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  let ef := (f.strictMono.strictMonoOn .univ).orderIso
  let eg := (g.strictMono.strictMonoOn .univ).orderIso
  let i : f '' .univ ≃o g '' .univ :=
    { __ := Equiv.setCongr (by simpa using! h)
      map_rel_iff' := by rfl }
  have : (ef.trans i).trans 

中文:
引理 OrderEmbedding.range_eq_iff
  证明: by
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  let ef := (f.strictMono.strictMonoOn .univ).orderIso
  let eg := (g.strictMono.strictMonoOn .univ).orderIso
  let i : f '' .univ ≃o g '' .univ :=
    { __ := Equiv.setCongr (by simpa using! h)
      map_rel_iff' := by rfl }
  have : (ef.trans i).trans 

Depends on / 依赖: Equiv.setCongr, OrderIso, OrderIso.apply_symm_apply, OrderIso.refl_apply, OrderIso.trans_apply, Set.mem_univ, Subsingleton, Subsingleton.elim, Subtype, Subtype.ext_iff, apply_symm_apply, ef.trans, eg.symm, ext_iff, f.strictMono.strictMonoOn, g.strictMono.strictMonoOn, map_rel_iff, mem_univ, orderIso, refl_apply
-/
lemma OrderEmbedding.range_eq_iff
    {α β : Type*} [LinearOrder α] [PartialOrder β] [Finite α]
    {f g : α ↪o β} :
    Set.range f = Set.range g ↔ f = g := by
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  let ef := (f.strictMono.strictMonoOn .univ).orderIso
  let eg := (g.strictMono.strictMonoOn .univ).orderIso
  let i : f '' .univ ≃o g '' .univ :=
    { __ := Equiv.setCongr (by simpa using! h)
      map_rel_iff' := by rfl }
  have : (ef.trans i).trans eg.symm = .refl _ := by
    exact Subsingleton.elim _ _
  ext x
  simpa only [OrderIso.trans_apply, OrderIso.apply_symm_apply, OrderIso.refl_apply, Subtype.ext_iff]
    using! congr(eg ($this ⟨x, Set.mem_univ x⟩))

/--
lemma `OrderHom.range_eq_iff` / 引理 `OrderHom.range_eq_iff`

English:
lemma OrderHom.range_eq_iff
  statement: {α β : Type*} [LinearOrder α] [PartialOrder β]
  proof: by
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  ext : 2
  exact DFunLike.congr_fun ((OrderEmbedding.range_eq_iff
    (f := .ofStrictMono f (f.monotone.strictMono_of_injective hf))
    (g := .ofStrictMono g (g.monotone.strictMono_of_injective hg))).1 (by simpa)) _

中文:
引理 序态射.range_eq_iff
  结论: {α β : 类型} [线性序 α] [偏序 β]
  证明: by
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  ext : 2
  exact DFunLike.congr_fun ((OrderEmbedding.range_eq_iff
    (f := .ofStrictMono f (f.monotone.strictMono_of_injective hf))
    (g := .ofStrictMono g (g.monotone.strictMono_of_injective hg))).1 (by simpa)) _

Depends on / 依赖: DFunLike, DFunLike.congr_fun, OrderEmbedding, OrderEmbedding.range_eq_iff, congr_fun, f.monotone.strictMono_of_injective, g.monotone.strictMono_of_injective, monotone, ofStrictMono, range_eq_iff, strictMono_of_injective
-/
lemma OrderHom.range_eq_iff {α β : Type*} [LinearOrder α] [PartialOrder β]
    [Finite α] {f g : α ->o β}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Set.range f = Set.range g ↔ f = g := by
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  ext : 2
  exact DFunLike.congr_fun ((OrderEmbedding.range_eq_iff
    (f := .ofStrictMono f (f.monotone.strictMono_of_injective hf))
    (g := .ofStrictMono g (g.monotone.strictMono_of_injective hg))).1 (by simpa)) _

/--
lemma `OrderHom.eq_id_of_injective` / 引理 `OrderHom.eq_id_of_injective`

English:
lemma OrderHom.eq_id_of_injective
  statement: {α : Type*} [LinearOrder α] [Finite α] (f : α ->o α)
  proof: (range_eq_iff hf Function.injective_id).1 (by
    simpa [Set.range_eq_univ] using Finite.surjective_of_injective hf)

中文:
引理 序态射.eq_id_of_injective
  结论: {α : 类型} [线性序 α] [有限 α] (f : α ->o α)
  证明: (range_eq_iff hf Function.injective_id).1 (by
    simpa [Set.range_eq_univ] using Finite.surjective_of_injective hf)

Depends on / 依赖: Finite, Finite.surjective_of_injective, Function, Function.injective_id, Set.range_eq_univ, injective_id, range_eq_iff, range_eq_univ, surjective_of_injective
-/
lemma OrderHom.eq_id_of_injective {α : Type*} [LinearOrder α] [Finite α] (f : α ->o α)
    (hf : Function.Injective f) :
    f = .id :=
  (range_eq_iff hf Function.injective_id).1 (by
    simpa [Set.range_eq_univ] using Finite.surjective_of_injective hf)

/--
theorem `StrictMono.eq_id` / 定理 `StrictMono.eq_id`

English:
theorem StrictMono.eq_id
  statement: {α : Type*} [LinearOrder α] [Finite α] {f : α -> α}
  proof: le_antisymm hf.le_id hf.id_le

中文:
定理 严格递增.eq_id
  结论: {α : 类型} [线性序 α] [有限 α] {f : α -> α}
  证明: le_antisymm hf.le_id hf.id_le

Depends on / 依赖: hf.id_le, hf.le_id, id_le, le_antisymm, le_id
-/
theorem StrictMono.eq_id {α : Type*} [LinearOrder α] [Finite α] {f : α -> α}
    (hf : StrictMono f) : f = id :=
  le_antisymm hf.le_id hf.id_le

/--
theorem `StrictMono.apply_eq` / 定理 `StrictMono.apply_eq`

English:
theorem StrictMono.apply_eq
  statement: {α : Type*} [LinearOrder α] [Finite α] {f : α -> α}
  proof: congrFun hf.eq_id x

中文:
定理 严格递增.apply_eq
  结论: {α : 类型} [线性序 α] [有限 α] {f : α -> α}
  证明: congrFun hf.eq_id x

Depends on / 依赖: eq_id, hf.eq_id
-/
theorem StrictMono.apply_eq {α : Type*} [LinearOrder α] [Finite α] {f : α -> α}
    {x : α} (hf : StrictMono f) : f x = x :=
  congrFun hf.eq_id x
