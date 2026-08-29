/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Basic
public import Mathlib.SetTheory.Ordinal.Family
public import Mathlib.SetTheory.Ordinal.Univ

/-!
# Enumerating a cofinal set

We define a typeclass `IsRegularCardinalOrder` for well-ordered types, whose order type equals (the
initial ordinal of) their cofinality. This notion does not appear in the literature, but intends to
generalize the properties of intervals `Iio c.ord`, wherever `c` is a regular cardinal. Other
instances of this typeclass include `ℕ`, `Ordinal`, and `Cardinal`.

If `s` is a cofinal subset of a regular cardinal order `α`, there exists a unique order isomorphism
`α ≃o s`, which we call `Order.enum`. When `α = Ordinal`, this is referred to as the enumerator
function of the set. Note that if `α = ℕ`, then this definition matches `Nat.nth`.

## Main results

- `Order.enum_eq_iff`: `Order.enum s _` is the unique strictly monotonic function with range `s`.
- `Order.isNormal_enum_iff_dirSupClosed`: club sets correspond one to one with normal functions.

## TODO

- Deprecate `Ordinal.enumOrd` in favor of `Order.enum`.
- Prove that `Order.enum` on the naturals coincides with `Nat.nth`.
-/

public section

universe u

open Cardinal Order Ordinal Set

variable {α : Type*}

/--
Definition of `IsRegularCardinalOrder` / `IsRegularCardinalOrder` 的定义

English:
class IsRegularCardinalOrder
  parameters: (α : Type*) [LinearOrder α] [WellFoundedLT α]
  axioms and operations (1):
    - type_lt_le_ord_cof : typeLT α <= (cof α).ord

中文:
类 IsRegularCardinalOrder
  参数: (α : 类型) [LinearOrder α] [WellFoundedLT α]
  公理与运算 (1 个):
    - type_lt_le_ord_cof : typeLT α <= (cof α).ord
-/
class IsRegularCardinalOrder (α : Type*) [LinearOrder α] [WellFoundedLT α] where
  type_lt_le_ord_cof : typeLT α <= (cof α).ord

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsRegularCardinalOrder Nat
  body: ⟨by simp⟩

中文:
实例 :
  签名: IsRegularCardinalOrder 自然数
  定义体: ⟨by simp⟩
-/
instance : IsRegularCardinalOrder Nat := ⟨by simp⟩

instance (priority := low) [LinearOrder α] [WellFoundedLT α] [Subsingleton α] :
    IsRegularCardinalOrder α where
  type_lt_le_ord_cof := by
    cases isEmpty_or_nonempty α
    · simpa
    · cases nonempty_unique α
      have := BoundedOrder.ofUnique α
      simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsRegularCardinalOrder Ordinal
  body: by
    rw [type_lt_ordinal]; rw [← ord_univ]; rw [ord_le_ord]; rw [le_cof_iff]
    intro s hs
    contrapose! hs
    rw [← Cardinal.lift_id (#s)]; rw [← small_iff_lift_mk_lt_univ] at hs
    rw [not_isCofinal_iff_bddAbove]
    exact Ordinal.bddAbove_of_small

中文:
实例 :
  签名: IsRegularCardinalOrder Ordinal
  定义体: by
    rw [type_lt_ordinal]; rw [← ord_univ]; rw [ord_le_ord]; rw [le_cof_iff]
    intro s hs
    contrapose! hs
    rw [← Cardinal.lift_id (#s)]; rw [← small_iff_lift_mk_lt_univ] at hs
    rw [not_isCofinal_iff_bddAbove]
    exact Ordinal.bddAbove_of_small

Depends on / 依赖: Cardinal, Cardinal.lift_id, Ordinal, Ordinal.bddAbove_of_small, bddAbove_of_small, contrapose, le_cof_iff, lift_id, not_isCofinal_iff_bddAbove, ord_le_ord, ord_univ, small_iff_lift_mk_lt_univ, type_lt_ordinal
-/
instance : IsRegularCardinalOrder Ordinal where
  type_lt_le_ord_cof := by
    rw [type_lt_ordinal]; rw [← ord_univ]; rw [ord_le_ord]; rw [le_cof_iff]
    intro s hs
    contrapose! hs
    rw [← Cardinal.lift_id (#s)]; rw [← small_iff_lift_mk_lt_univ] at hs
    rw [not_isCofinal_iff_bddAbove]
    exact Ordinal.bddAbove_of_small

namespace Order
variable [LinearOrder α] [WellFoundedLT α] [IsRegularCardinalOrder α]

/--
theorem `ord_cof_eq_type_lt` / 定理 `ord_cof_eq_type_lt`

English:
theorem ord_cof_eq_type_lt
  statement: (cof α).ord = typeLT α
  proof: by
  apply IsRegularCardinalOrder.type_lt_le_ord_cof.antisymm'
  rw [ord_le]; rw [card_type]
  exact cof_le_cardinalMk α

@[simp]

中文:
定理 ord_cof_eq_type_lt
  结论: (cof α).ord = typeLT α
  证明: by
  apply IsRegularCardinalOrder.type_lt_le_ord_cof.antisymm'
  rw [ord_le]; rw [card_type]
  exact cof_le_cardinalMk α

@[simp]

Depends on / 依赖: IsRegularCardinalOrder, IsRegularCardinalOrder.type_lt_le_ord_cof.antisymm, antisymm, card_type, cof_le_cardinalMk, ord_le, type_lt_le_ord_cof
-/
theorem ord_cof_eq_type_lt : (cof α).ord = typeLT α := by
  apply IsRegularCardinalOrder.type_lt_le_ord_cof.antisymm'
  rw [ord_le]; rw [card_type]
  exact cof_le_cardinalMk α

@[simp]
/--
theorem `cof_eq_cardinalMk` / 定理 `cof_eq_cardinalMk`

English:
theorem cof_eq_cardinalMk
  statement: cof α = #α
  proof: by
  rw [← card_type LT.lt]; rw [← ord_cof_eq_type_lt]; rw [card_ord]

@[simp]

中文:
定理 cof_eq_cardinalMk
  结论: cof α = #α
  证明: by
  rw [← card_type LT.lt]; rw [← ord_cof_eq_type_lt]; rw [card_ord]

@[simp]

Depends on / 依赖: LT.lt, card_ord, card_type, ord_cof_eq_type_lt
-/
theorem cof_eq_cardinalMk : cof α = #α := by
  rw [← card_type LT.lt]; rw [← ord_cof_eq_type_lt]; rw [card_ord]

@[simp]
/--
theorem `_root_.Cardinal.ord_cardinalMk` / 定理 `_root_.Cardinal.ord_cardinalMk`

English:
theorem _root_.Cardinal.ord_cardinalMk
  statement: ord #α = typeLT α
  proof: by
  rw [← ord_cof_eq_type_lt]; rw [cof_eq_cardinalMk]

中文:
定理 _root_.Cardinal.ord_cardinalMk
  结论: ord #α = typeLT α
  证明: by
  rw [← ord_cof_eq_type_lt]; rw [cof_eq_cardinalMk]

Depends on / 依赖: cof_eq_cardinalMk, ord_cof_eq_type_lt
-/
theorem _root_.Cardinal.ord_cardinalMk : ord #α = typeLT α := by
  rw [← ord_cof_eq_type_lt]; rw [cof_eq_cardinalMk]

/--
theorem `cof_ordinal` / 定理 `cof_ordinal`

English:
theorem cof_ordinal
  statement: cof Ordinal.{u} = Cardinal.univ.{u, u + 1}
  proof: by
  simp

中文:
定理 cof_ordinal
  结论: cof Ordinal.{u} = Cardinal.univ.{u, u + 1}
  证明: by
  simp
-/
theorem cof_ordinal : cof Ordinal.{u} = Cardinal.univ.{u, u + 1} := by
  simp

/--
theorem `type_eq_of_isCofinal` / 定理 `type_eq_of_isCofinal`

English:
theorem type_eq_of_isCofinal
  given: {s : Set α} (hs : IsCofinal s)
  statement: typeLT s = typeLT α
  proof: by
  apply (RelEmbedding.ofMonotone Subtype.val (by simp)).ordinal_type_le.antisymm
  rw [← ord_cardinalMk]; rw [ord_le]; rw [card_type]; rw [← cof_eq_cardinalMk]
  exact cof_le hs

中文:
定理 type_eq_of_isCofinal
  条件: {s : Set α} (hs : IsCofinal s)
  结论: typeLT s = typeLT α
  证明: by
  apply (RelEmbedding.ofMonotone Subtype.val (by simp)).ordinal_type_le.antisymm
  rw [← ord_cardinalMk]; rw [ord_le]; rw [card_type]; rw [← cof_eq_cardinalMk]
  exact cof_le hs

Depends on / 依赖: RelEmbedding, RelEmbedding.ofMonotone, Subtype, Subtype.val, antisymm, card_type, cof_eq_cardinalMk, cof_le, ofMonotone, ord_cardinalMk, ord_le, ordinal_type_le, ordinal_type_le.antisymm
-/
theorem type_eq_of_isCofinal {s : Set α} (hs : IsCofinal s) : typeLT s = typeLT α := by
  apply (RelEmbedding.ofMonotone Subtype.val (by simp)).ordinal_type_le.antisymm
  rw [← ord_cardinalMk]; rw [ord_le]; rw [card_type]; rw [← cof_eq_cardinalMk]
  exact cof_le hs

/--
Definition of `enum` / `enum` 的定义

English:
definition enum
  signature: (s : Set α) (hs : IsCofinal s)
  body: .ofRelIsoLT (type_eq.1 (type_eq_of_isCofinal hs).symm).some

中文:
定义 enum
  签名: (s : Set α) (hs : IsCofinal s)
  定义体: .ofRelIsoLT (type_eq.1 (type_eq_of_isCofinal hs).symm).some

Depends on / 依赖: ofRelIsoLT, type_eq, type_eq_of_isCofinal
-/
noncomputable def enum (s : Set α) (hs : IsCofinal s) : α ≃o s :=
  .ofRelIsoLT (type_eq.1 (type_eq_of_isCofinal hs).symm).some

variable {s : Set α} {hs : IsCofinal s}

/--
theorem `enum_le_of_forall_lt` / 定理 `enum_le_of_forall_lt`

English:
theorem enum_le_of_forall_lt
  given: {a o : α} (ho : o in s) (H : forall b < a, enum s hs b < o)
  proof: by
  rw [← Subtype.coe_mk o ho]; rw [Subtype.coe_le_coe]; rw [← OrderIso.le_symm_apply]
  apply le_of_forall_lt
  simpa [OrderIso.lt_symm_apply]

中文:
定理 enum_le_of_forall_lt
  条件: {a o : α} (ho : o in s) (H : 对任意 b < a, enum s hs b < o)
  证明: by
  rw [← Subtype.coe_mk o ho]; rw [Subtype.coe_le_coe]; rw [← OrderIso.le_symm_apply]
  apply le_of_forall_lt
  simpa [OrderIso.lt_symm_apply]

Depends on / 依赖: OrderIso, OrderIso.le_symm_apply, OrderIso.lt_symm_apply, Subtype, Subtype.coe_le_coe, Subtype.coe_mk, coe_le_coe, coe_mk, le_of_forall_lt, le_symm_apply, lt_symm_apply
-/
theorem enum_le_of_forall_lt {a o : α} (ho : o in s) (H : forall b < a, enum s hs b < o) :
    enum s hs a <= o := by
  rw [← Subtype.coe_mk o ho]; rw [Subtype.coe_le_coe]; rw [← OrderIso.le_symm_apply]
  apply le_of_forall_lt
  simpa [OrderIso.lt_symm_apply]

/--
theorem `enum_succ_le_of_lt` / 定理 `enum_succ_le_of_lt`

English:
theorem enum_succ_le_of_lt
  given: [SuccOrder α] {a o : α} (ha : o in s) (H : enum s hs a < o)
  proof: by
  refine enum_le_of_forall_lt ha fun b hb => H.trans_le' ?_
  simpa using le_of_lt_succ hb

@[simp]

中文:
定理 enum_succ_le_of_lt
  条件: [SuccOrder α] {a o : α} (ha : o in s) (H : enum s hs a < o)
  证明: by
  refine enum_le_of_forall_lt ha fun b hb => H.trans_le' ?_
  simpa using le_of_lt_succ hb

@[simp]

Depends on / 依赖: H.trans_le, enum_le_of_forall_lt, le_of_lt_succ, trans_le
-/
theorem enum_succ_le_of_lt [SuccOrder α] {a o : α} (ha : o in s) (H : enum s hs a < o) :
    enum s hs (succ a) <= o := by
  refine enum_le_of_forall_lt ha fun b hb => H.trans_le' ?_
  simpa using le_of_lt_succ hb

@[simp]
/--
theorem `enum_univ` / 定理 `enum_univ`

English:
theorem enum_univ
  given: (x : α)
  statement: enum univ .univ x = ⟨x, mem_univ x⟩
  proof: by
  rw [← Subsingleton.allEq OrderIso.Set.univ.symm (enum univ .univ)]
  rfl

中文:
定理 enum_univ
  条件: (x : α)
  结论: enum univ .univ x = ⟨x, mem_univ x⟩
  证明: by
  rw [← Subsingleton.allEq OrderIso.Set.univ.symm (enum univ .univ)]
  rfl

Depends on / 依赖: OrderIso, OrderIso.Set.univ.symm, Subsingleton, Subsingleton.allEq
-/
theorem enum_univ (x : α) : enum univ .univ x = ⟨x, mem_univ x⟩ := by
  rw [← Subsingleton.allEq OrderIso.Set.univ.symm (enum univ .univ)]
  rfl

/--
theorem `enum_anti` / 定理 `enum_anti`

English:
theorem enum_anti
  given: {hs : IsCofinal s} {t : Set α} {x : α} (h : s subseteq t)
  proof: by
  induction x using WellFoundedLT.induction with | ind x IH
  exact enum_le_of_forall_lt (h (Subtype.prop _)) fun y hy =>
    (IH y hy).trans_lt ((enum s hs).strictMono hy)

中文:
定理 enum_anti
  条件: {hs : IsCofinal s} {t : Set α} {x : α} (h : s subseteq t)
  证明: by
  induction x using WellFoundedLT.induction with | ind x IH
  exact enum_le_of_forall_lt (h (Subtype.prop _)) fun y hy =>
    (IH y hy).trans_lt ((enum s hs).strictMono hy)

Depends on / 依赖: Subtype, Subtype.prop, WellFoundedLT, WellFoundedLT.induction, enum_le_of_forall_lt, strictMono, trans_lt
-/
theorem enum_anti {hs : IsCofinal s} {t : Set α} {x : α} (h : s subseteq t) :
    enum t (hs.mono h) x <= (enum s hs x).1 := by
  induction x using WellFoundedLT.induction with | ind x IH
  exact enum_le_of_forall_lt (h (Subtype.prop _)) fun y hy =>
    (IH y hy).trans_lt ((enum s hs).strictMono hy)

/--
theorem `enum_eq_iff` / 定理 `enum_eq_iff`

English:
theorem enum_eq_iff
  given: {f : α -> α}
  statement: Subtype.val ∘ enum s hs = f ↔ StrictMono f ∧ range f = s
  proof: by
  have H := (Subtype.strictMono_coe _).comp (enum s hs).strictMono
  constructor
  · rintro rfl
    use (Subtype.strictMono_coe _).comp (enum s hs).strictMono
    simp
  · rintro ⟨hf, rfl⟩
    rw [← StrictMono.range_inj H hf]
    simp
    rfl

中文:
定理 enum_eq_iff
  条件: {f : α -> α}
  结论: Subtype.val ∘ enum s hs = f ↔ StrictMono f ∧ range f = s
  证明: by
  have H := (Subtype.strictMono_coe _).comp (enum s hs).strictMono
  constructor
  · rintro rfl
    use (Subtype.strictMono_coe _).comp (enum s hs).strictMono
    simp
  · rintro ⟨hf, rfl⟩
    rw [← StrictMono.range_inj H hf]
    simp
    rfl

Depends on / 依赖: StrictMono, StrictMono.range_inj, Subtype, Subtype.strictMono_coe, range_inj, strictMono, strictMono_coe
-/
theorem enum_eq_iff {f : α -> α} : Subtype.val ∘ enum s hs = f ↔ StrictMono f ∧ range f = s := by
  have H := (Subtype.strictMono_coe _).comp (enum s hs).strictMono
  constructor
  · rintro rfl
    use (Subtype.strictMono_coe _).comp (enum s hs).strictMono
    simp
  · rintro ⟨hf, rfl⟩
    rw [← StrictMono.range_inj H hf]
    simp
    rfl

/--
theorem `enum_range` / 定理 `enum_range`

English:
theorem enum_range
  given: {f : α -> α} (hf : StrictMono f)
  proof: by
  ext x
  apply congrFun (enum_eq_iff.2 ⟨?_, ?_⟩)
  · exact (Subtype.strictMono_coe _).comp (OrderIso.strictMono _)
  · simp

中文:
定理 enum_range
  条件: {f : α -> α} (hf : StrictMono f)
  证明: by
  ext x
  apply congrFun (enum_eq_iff.2 ⟨?_, ?_⟩)
  · exact (Subtype.strictMono_coe _).comp (OrderIso.strictMono _)
  · simp

Depends on / 依赖: OrderIso, OrderIso.strictMono, Subtype, Subtype.strictMono_coe, enum_eq_iff, strictMono, strictMono_coe
-/
theorem enum_range {f : α -> α} (hf : StrictMono f) :
    enum (range f) (isCofinal_range_of_strictMono hf) = hf.orderIso := by
  ext x
  apply congrFun (enum_eq_iff.2 ⟨?_, ?_⟩)
  · exact (Subtype.strictMono_coe _).comp (OrderIso.strictMono _)
  · simp

/--
theorem `enum_bot` / 定理 `enum_bot`

English:
theorem enum_bot
  statement: {α : Type*} [ConditionallyCompleteLinearOrderBot α] [WellFoundedLT α]
  proof: by
  let : Bot s := ⟨⟨sInf s, csInf_mem hs.nonempty⟩⟩
  let : OrderBot s := .mk fun a => csInf_le' a.2
  rw [OrderIso.map_bot]
  rfl

中文:
定理 enum_bot
  结论: {α : 类型} [ConditionallyCompleteLinearOrderBot α] [WellFoundedLT α]
  证明: by
  let : Bot s := ⟨⟨sInf s, csInf_mem hs.nonempty⟩⟩
  let : OrderBot s := .mk fun a => csInf_le' a.2
  rw [OrderIso.map_bot]
  rfl

Depends on / 依赖: OrderBot, OrderIso, OrderIso.map_bot, csInf_le, csInf_mem, hs.nonempty, map_bot, nonempty
-/
theorem enum_bot {α : Type*} [ConditionallyCompleteLinearOrderBot α] [WellFoundedLT α]
    [IsRegularCardinalOrder α] {s : Set α} {hs : IsCofinal s} : enum s hs ⊥ = sInf s := by
  let : Bot s := ⟨⟨sInf s, csInf_mem hs.nonempty⟩⟩
  let : OrderBot s := .mk fun a => csInf_le' a.2
  rw [OrderIso.map_bot]
  rfl

/--
theorem `isNormal_enum_iff_dirSupClosed` / 定理 `isNormal_enum_iff_dirSupClosed`

English:
theorem isNormal_enum_iff_dirSupClosed
  proof: by
  let H := (Subtype.strictMono_coe _).comp (enum s hs).strictMono
  refine ⟨fun he => by simpa using he.dirSupClosed_range, ?_⟩
  rw [isNormal_iff]; rw [dirSupClosed_iff_of_linearOrder]
  refine fun hs' => ⟨H, fun a ha b hb => ?_⟩
  have bdd : BddAbove (Subtype.val ∘ enum s hs '' Iio a) := by
   

中文:
定理 isNormal_enum_iff_dirSupClosed
  证明: by
  let H := (Subtype.strictMono_coe _).comp (enum s hs).strictMono
  refine ⟨fun he => by simpa using he.dirSupClosed_range, ?_⟩
  rw [isNormal_iff]; rw [dirSupClosed_iff_of_linearOrder]
  refine fun hs' => ⟨H, fun a ha b hb => ?_⟩
  have bdd : BddAbove (Subtype.val ∘ enum s hs '' Iio a) := by
   

Depends on / 依赖: BddAbove, Nonempty, Subtype, Subtype.strictMono_coe, Subtype.val, WellFoundedLT, WellFoundedLT.conditionallyCompleteLinearOrderBot, WellFoundedLT.toOrderBot, conditionallyCompleteLinearOrderBot, dirSupClosed_iff_of_linearOrder, dirSupClosed_range, he.dirSupClosed_range, hx.le, isNormal_iff, strictMono, strictMono_coe, toOrderBot, upperBounds
-/
theorem isNormal_enum_iff_dirSupClosed :
    IsNormal (Subtype.val ∘ enum s hs) ↔ DirSupClosed s := by
  let H := (Subtype.strictMono_coe _).comp (enum s hs).strictMono
  refine ⟨fun he => by simpa using he.dirSupClosed_range, ?_⟩
  rw [isNormal_iff]; rw [dirSupClosed_iff_of_linearOrder]
  refine fun hs' => ⟨H, fun a ha b hb => ?_⟩
  have bdd : BddAbove (Subtype.val ∘ enum s hs '' Iio a) := by
    use enum s hs a
    simpa [upperBounds] using fun x hx => hx.le
  have : Nonempty α := ⟨a⟩
  let := WellFoundedLT.toOrderBot α
  let := WellFoundedLT.conditionallyCompleteLinearOrderBot α
  trans sSup ((Subtype.val ∘ enum s hs) '' Iio a)
  · refine enum_le_of_forall_lt (hs' ?_ ?_ (isLUB_csSup' bdd)) fun b hb => ?_
    · grind
    · simpa using ha.ne_bot
    · obtain ⟨c, hca, hbc⟩ := ha.lt_iff_exists_lt.1 hb
refine (H hbc).trans_le le_csSup bdd ⟨c, ?_⟩
      simpa
  · apply csSup_le'
    simpa [upperBounds]

end Order
