/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.Ring.Canonical
public import Mathlib.Data.Fintype.Option
public import Mathlib.Order.InitialSeg
public import Mathlib.Order.Nat
public import Mathlib.Order.SuccPred.CompleteLinearOrder
public import Mathlib.SetTheory.Cardinal.Defs
public import Mathlib.SetTheory.Cardinal.SchroederBernstein

/-!
# Order on cardinal numbers

We define the order on cardinal numbers and show its basic properties, including the ordered
semiring structure.

## Main definitions

* The order `c₁ ≤ c₂` is defined by `Cardinal.le_def α β : #α ≤ #β ↔ Nonempty (α ↪ β)`.
* `Order.IsSuccLimit c` means that `c` is a (weak) limit cardinal: `c ≠ 0 ∧ ∀ x < c, succ x < c`.
* `Cardinal.IsStrongLimit c` means that `c` is a strong limit cardinal:
  `c ≠ 0 ∧ ∀ x < c, 2 ^ x < c`.

## Main instances

* Cardinals form a `CanonicallyOrderedAdd` `OrderedCommSemiring` with the aforementioned sum and
  product.
* Cardinals form a `SuccOrder`. Use `Order.succ c` for the smallest cardinal greater than `c`.
* The less-than relation on cardinals forms a well-order.
* Cardinals form a `ConditionallyCompleteLinearOrderBot`. Bounded sets for cardinals in universe
  `u` are precisely the sets indexed by some type in universe `u`, see
  `Cardinal.bddAbove_iff_small`. One can use `sSup` for the cardinal supremum,
  and `sInf` for the minimum of a set of cardinals.

## Main statements

* Cantor's theorem: `Cardinal.cantor c : c < 2 ^ c`.
* König's theorem: `Cardinal.sum_lt_prod`

## Implementation notes

The current setup interweaves the order structure and the algebraic structure on `Cardinal` tightly.
For example, we need to know what a ring is in order to show that `0` is the smallest cardinality.
That is reflected in this file containing both the order and algebra structure.

## References

* <https://en.wikipedia.org/wiki/Cardinal_number>

## Tags

cardinal number, cardinal arithmetic, cardinal exponentiation, aleph,
Cantor's theorem, König's theorem, Konig's theorem
-/

@[expose] public section

assert_not_exists Field

open List Function Order Set

noncomputable section

universe u v w v' w'

variable {α β : Type u}

namespace Cardinal

/-! ### Order on cardinals -/

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE Cardinal.{u}
  body: ⟨fun q₁ q₂ =>
    Quotient.liftOn₂ q₁ q₂ (fun α β => Nonempty <| α ↪ β) fun _ _ _ _ ⟨e₁⟩ ⟨e₂⟩ =>
      propext ⟨fun ⟨e⟩ => ⟨e.congr e₁ e₂⟩, fun ⟨e⟩ => ⟨e.congr e₁.symm e₂.symm⟩⟩⟩

中文:
实例 :
  签名: LE Cardinal.{u}
  定义体: ⟨fun q₁ q₂ =>
    Quotient.liftOn₂ q₁ q₂ (fun α β => Nonempty <| α ↪ β) fun _ _ _ _ ⟨e₁⟩ ⟨e₂⟩ =>
      propext ⟨fun ⟨e⟩ => ⟨e.congr e₁ e₂⟩, fun ⟨e⟩ => ⟨e.congr e₁.symm e₂.symm⟩⟩⟩

Depends on / 依赖: Nonempty, Quotient, Quotient.liftOn, e.congr, propext
-/
instance : LE Cardinal.{u} :=
  ⟨fun q₁ q₂ =>
    Quotient.liftOn₂ q₁ q₂ (fun α β => Nonempty <| α ↪ β) fun _ _ _ _ ⟨e₁⟩ ⟨e₂⟩ =>
      propext ⟨fun ⟨e⟩ => ⟨e.congr e₁ e₂⟩, fun ⟨e⟩ => ⟨e.congr e₁.symm e₂.symm⟩⟩⟩

/--
Instance `partialOrder` / 实例 `partialOrder`

English:
instance partialOrder
  signature: : PartialOrder Cardinal.{u} where
  body: by
    rintro ⟨α⟩
    exact ⟨Embedding.refl _⟩
  le_trans := by
    rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨e₁⟩ ⟨e₂⟩
    exact ⟨e₁.trans e₂⟩
  le_antisymm := by
    rintro ⟨α⟩ ⟨β⟩ ⟨e₁⟩ ⟨e₂⟩
    exact Quotient.sound (e₁.antisymm e₂)

中文:
实例 partialOrder
  签名: : PartialOrder Cardinal.{u} where
  定义体: by
    rintro ⟨α⟩
    exact ⟨Embedding.refl _⟩
  le_trans := by
    rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨e₁⟩ ⟨e₂⟩
    exact ⟨e₁.trans e₂⟩
  le_antisymm := by
    rintro ⟨α⟩ ⟨β⟩ ⟨e₁⟩ ⟨e₂⟩
    exact Quotient.sound (e₁.antisymm e₂)

Depends on / 依赖: Embedding, Embedding.refl, Quotient, Quotient.sound, antisymm, le_antisymm, le_trans
-/
instance partialOrder : PartialOrder Cardinal.{u} where
  le_refl := by
    rintro ⟨α⟩
    exact ⟨Embedding.refl _⟩
  le_trans := by
    rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨e₁⟩ ⟨e₂⟩
    exact ⟨e₁.trans e₂⟩
  le_antisymm := by
    rintro ⟨α⟩ ⟨β⟩ ⟨e₁⟩ ⟨e₂⟩
    exact Quotient.sound (e₁.antisymm e₂)

/--
Instance `linearOrder` / 实例 `linearOrder`

English:
instance linearOrder
  signature: : LinearOrder Cardinal.{u}
  body: { Cardinal.partialOrder with
    le_total := by
      rintro ⟨α⟩ ⟨β⟩
      apply Embedding.total
    toDecidableLE := Classical.decRel _ }

中文:
实例 linearOrder
  签名: : LinearOrder Cardinal.{u}
  定义体: { Cardinal.partialOrder with
    le_total := by
      rintro ⟨α⟩ ⟨β⟩
      apply Embedding.total
    toDecidableLE := Classical.decRel _ }

Depends on / 依赖: Cardinal, Cardinal.partialOrder, Classical, Classical.decRel, Embedding, Embedding.total, decRel, le_total, partialOrder, toDecidableLE
-/
instance linearOrder : LinearOrder Cardinal.{u} :=
  { Cardinal.partialOrder with
    le_total := by
      rintro ⟨α⟩ ⟨β⟩
      apply Embedding.total
    toDecidableLE := Classical.decRel _ }

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: (α β : Type u)
  statement: #α <= #β ↔ Nonempty (α ↪ β)
  proof: Iff.rfl

中文:
定理 le_def
  条件: (α β : 类型u)
  结论: #α <= #β ↔ Nonempty (α ↪ β)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def (α β : Type u) : #α <= #β ↔ Nonempty (α ↪ β) :=
  Iff.rfl

/--
theorem `mk_le_of_injective` / 定理 `mk_le_of_injective`

English:
theorem mk_le_of_injective
  given: {α β : Type u} {f : α -> β} (hf : Injective f)
  statement: #α <= #β
  proof: ⟨⟨f, hf⟩⟩

中文:
定理 mk_le_of_injective
  条件: {α β : 类型u} {f : α -> β} (hf : Injective f)
  结论: #α <= #β
  证明: ⟨⟨f, hf⟩⟩
-/
theorem mk_le_of_injective {α β : Type u} {f : α -> β} (hf : Injective f) : #α <= #β :=
  ⟨⟨f, hf⟩⟩

/--
theorem `_root_.Function.Embedding.cardinal_le` / 定理 `_root_.Function.Embedding.cardinal_le`

English:
theorem _root_.Function.Embedding.cardinal_le
  given: {α β : Type u} (f : α ↪ β)
  statement: #α <= #β
  proof: ⟨f⟩

中文:
定理 _root_.Function.Embedding.cardinal_le
  条件: {α β : 类型u} (f : α ↪ β)
  结论: #α <= #β
  证明: ⟨f⟩
-/
theorem _root_.Function.Embedding.cardinal_le {α β : Type u} (f : α ↪ β) : #α <= #β :=
  ⟨f⟩

/--
theorem `mk_le_of_surjective` / 定理 `mk_le_of_surjective`

English:
theorem mk_le_of_surjective
  given: {α β : Type u} {f : α -> β} (hf : Surjective f)
  statement: #β <= #α
  proof: ⟨Embedding.ofSurjective f hf⟩

中文:
定理 mk_le_of_surjective
  条件: {α β : 类型u} {f : α -> β} (hf : Surjective f)
  结论: #β <= #α
  证明: ⟨Embedding.ofSurjective f hf⟩

Depends on / 依赖: Embedding, Embedding.ofSurjective, ofSurjective
-/
theorem mk_le_of_surjective {α β : Type u} {f : α -> β} (hf : Surjective f) : #β <= #α :=
  ⟨Embedding.ofSurjective f hf⟩

/--
theorem `le_mk_iff_exists_set` / 定理 `le_mk_iff_exists_set`

English:
theorem le_mk_iff_exists_set
  given: {c : Cardinal} {α : Type u}
  statement: c <= #α ↔ exists p : Set α, #p = c
  proof: ⟨inductionOn c fun _ ⟨⟨f, hf⟩⟩ => ⟨Set.range f, (Equiv.ofInjective f hf).cardinal_eq.symm⟩,
    fun ⟨_, e⟩ => e ▸ ⟨⟨Subtype.val, fun _ _ => Subtype.ext⟩⟩⟩

中文:
定理 le_mk_iff_exists_set
  条件: {c : Cardinal} {α : 类型u}
  结论: c <= #α ↔ 存在 p : Set α, #p = c
  证明: ⟨inductionOn c fun _ ⟨⟨f, hf⟩⟩ => ⟨Set.range f, (Equiv.ofInjective f hf).cardinal_eq.symm⟩,
    fun ⟨_, e⟩ => e ▸ ⟨⟨Subtype.val, fun _ _ => Subtype.ext⟩⟩⟩

Depends on / 依赖: Equiv.ofInjective, Set.range, Subtype, Subtype.ext, Subtype.val, cardinal_eq, cardinal_eq.symm, inductionOn, ofInjective
-/
theorem le_mk_iff_exists_set {c : Cardinal} {α : Type u} : c <= #α ↔ exists p : Set α, #p = c :=
  ⟨inductionOn c fun _ ⟨⟨f, hf⟩⟩ => ⟨Set.range f, (Equiv.ofInjective f hf).cardinal_eq.symm⟩,
    fun ⟨_, e⟩ => e ▸ ⟨⟨Subtype.val, fun _ _ => Subtype.ext⟩⟩⟩

/--
theorem `mk_subtype_le` / 定理 `mk_subtype_le`

English:
theorem mk_subtype_le
  given: {α : Type u} (p : α -> Prop)
  statement: #(Subtype p) <= #α
  proof: ⟨Embedding.subtype p⟩

中文:
定理 mk_subtype_le
  条件: {α : 类型u} (p : α -> 命题)
  结论: #(Subtype p) <= #α
  证明: ⟨Embedding.subtype p⟩

Depends on / 依赖: Embedding, Embedding.subtype, subtype
-/
theorem mk_subtype_le {α : Type u} (p : α -> Prop) : #(Subtype p) <= #α :=
  ⟨Embedding.subtype p⟩

/--
theorem `mk_set_le` / 定理 `mk_set_le`

English:
theorem mk_set_le
  given: (s : Set α)
  statement: #s <= #α
  proof: mk_subtype_le (· in s)

中文:
定理 mk_set_le
  条件: (s : Set α)
  结论: #s <= #α
  证明: mk_subtype_le (· in s)

Depends on / 依赖: mk_subtype_le
-/
theorem mk_set_le (s : Set α) : #s <= #α :=
  mk_subtype_le (· in s)

/--
theorem `out_embedding` / 定理 `out_embedding`

English:
theorem out_embedding
  given: {c c' : Cardinal}
  statement: c <= c' ↔ Nonempty (c.out ↪ c'.out)
  proof: by
  conv_lhs => rw [← Cardinal.mk_out c, ← Cardinal.mk_out c', le_def]

中文:
定理 out_embedding
  条件: {c c' : Cardinal}
  结论: c <= c' ↔ Nonempty (c.out ↪ c'.out)
  证明: by
  conv_lhs => rw [← Cardinal.mk_out c, ← Cardinal.mk_out c', le_def]

Depends on / 依赖: Cardinal, Cardinal.mk_out, conv_lhs, le_def, mk_out
-/
theorem out_embedding {c c' : Cardinal} : c <= c' ↔ Nonempty (c.out ↪ c'.out) := by
  conv_lhs => rw [← Cardinal.mk_out c, ← Cardinal.mk_out c', le_def]

/--
theorem `lift_mk_le` / 定理 `lift_mk_le`

English:
theorem lift_mk_le
  given: {α : Type v} {β : Type w}
  proof: ⟨fun ⟨f⟩ => ⟨Embedding.congr Equiv.ulift Equiv.ulift f⟩, fun ⟨f⟩ =>
    ⟨Embedding.congr Equiv.ulift.symm Equiv.ulift.symm f⟩⟩

中文:
定理 lift_mk_le
  条件: {α : 类型v} {β : Type w}
  证明: ⟨fun ⟨f⟩ => ⟨Embedding.congr Equiv.ulift Equiv.ulift f⟩, fun ⟨f⟩ =>
    ⟨Embedding.congr Equiv.ulift.symm Equiv.ulift.symm f⟩⟩

Depends on / 依赖: Embedding, Embedding.congr, Equiv.ulift, Equiv.ulift.symm
-/
theorem lift_mk_le {α : Type v} {β : Type w} :
    lift.{max u w} #α <= lift.{max u v} #β ↔ Nonempty (α ↪ β) :=
  ⟨fun ⟨f⟩ => ⟨Embedding.congr Equiv.ulift Equiv.ulift f⟩, fun ⟨f⟩ =>
    ⟨Embedding.congr Equiv.ulift.symm Equiv.ulift.symm f⟩⟩

/--
theorem `lift_mk_le'` / 定理 `lift_mk_le'`

English:
theorem lift_mk_le'
  given: {α : Type u} {β : Type v}
  statement: lift.{v} #α <= lift.{u} #β ↔ Nonempty (α ↪ β)
  proof: lift_mk_le.{0}

中文:
定理 lift_mk_le'
  条件: {α : 类型u} {β : 类型v}
  结论: lift.{v} #α <= lift.{u} #β ↔ Nonempty (α ↪ β)
  证明: lift_mk_le.{0}

Depends on / 依赖: lift_mk_le
-/
theorem lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #α <= lift.{u} #β ↔ Nonempty (α ↪ β) :=
  lift_mk_le.{0}

/-! ### `lift` sends `Cardinal.{u}` to an initial segment of `Cardinal.{max u v}`. -/

/-- `Cardinal.lift` as an `InitialSeg`. -/
@[simps!]
/--
Definition of `liftInitialSeg` / `liftInitialSeg` 的定义

English:
definition liftInitialSeg
  signature: : Cardinal.{u} <=i Cardinal.{max u v}
  body: by
  refine ⟨(OrderEmbedding.ofMapLEIff lift ?_).ltEmbedding, ?_⟩ <;> intro a b
  · refine inductionOn₂ a b fun _ _ => ?_
    rw [← lift_umax]; rw [lift_mk_le.{v]; rw [u]; rw [u}]; rw [le_def]
  · refine inductionOn₂ a b fun α β h => ?_
    obtain ⟨e⟩ := h.le
    replace e := e.congr (Equiv.refl β) 

中文:
定义 liftInitialSeg
  签名: : Cardinal.{u} <=i Cardinal.{max u v}
  定义体: by
  refine ⟨(OrderEmbedding.ofMapLEIff lift ?_).ltEmbedding, ?_⟩ <;> intro a b
  · refine inductionOn₂ a b fun _ _ => ?_
    rw [← lift_umax]; rw [lift_mk_le.{v]; rw [u]; rw [u}]; rw [le_def]
  · refine inductionOn₂ a b fun α β h => ?_
    obtain ⟨e⟩ := h.le
    replace e := e.congr (Equiv.refl β) 

Depends on / 依赖: Equiv.refl, Equiv.symm, Equiv.ulift, Equiv.ulift.trans, OrderEmbedding, OrderEmbedding.ofMapLEIff, codRestrict, e.codRestrict, e.congr, equivOfSurjective, h.le, le_def, lift_mk_le, lift_umax, ltEmbedding, mem_range_self, mk_congr, ofMapLEIff, replace
-/
def liftInitialSeg : Cardinal.{u} <=i Cardinal.{max u v} := by
  refine ⟨(OrderEmbedding.ofMapLEIff lift ?_).ltEmbedding, ?_⟩ <;> intro a b
  · refine inductionOn₂ a b fun _ _ => ?_
    rw [← lift_umax]; rw [lift_mk_le.{v]; rw [u]; rw [u}]; rw [le_def]
  · refine inductionOn₂ a b fun α β h => ?_
    obtain ⟨e⟩ := h.le
    replace e := e.congr (Equiv.refl β) Equiv.ulift
    refine ⟨#(range e), mk_congr (Equiv.ulift.trans <| Equiv.symm ?_)⟩
    apply (e.codRestrict _ mem_range_self).equivOfSurjective
    rintro ⟨a, ⟨b, rfl⟩⟩
    exact ⟨b, rfl⟩

/--
theorem `mem_range_lift_of_le` / 定理 `mem_range_lift_of_le`

English:
theorem mem_range_lift_of_le
  given: {a : Cardinal.{u}} {b : Cardinal.{max u v}}
  proof: liftInitialSeg.mem_range_of_le

中文:
定理 mem_range_lift_of_le
  条件: {a : Cardinal.{u}} {b : Cardinal.{max u v}}
  证明: liftInitialSeg.mem_range_of_le

Depends on / 依赖: liftInitialSeg, liftInitialSeg.mem_range_of_le, mem_range_of_le
-/
theorem mem_range_lift_of_le {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b <= lift.{v, u} a -> b in Set.range lift.{v, u} :=
  liftInitialSeg.mem_range_of_le

/--
theorem `lift_injective` / 定理 `lift_injective`

English:
theorem lift_injective
  statement: Injective lift.{u, v}
  proof: liftInitialSeg.injective

@[simp]

中文:
定理 lift_injective
  结论: Injective lift.{u, v}
  证明: liftInitialSeg.injective

@[simp]

Depends on / 依赖: injective, liftInitialSeg, liftInitialSeg.injective
-/
theorem lift_injective : Injective lift.{u, v} :=
  liftInitialSeg.injective

@[simp]
/--
theorem `lift_inj` / 定理 `lift_inj`

English:
theorem lift_inj
  given: {a b : Cardinal.{u}}
  statement: lift.{v, u} a = lift.{v, u} b ↔ a = b
  proof: lift_injective.eq_iff

@[simp]

中文:
定理 lift_inj
  条件: {a b : Cardinal.{u}}
  结论: lift.{v, u} a = lift.{v, u} b ↔ a = b
  证明: lift_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, lift_injective, lift_injective.eq_iff
-/
theorem lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.{v, u} b ↔ a = b :=
  lift_injective.eq_iff

@[simp]
/--
theorem `lift_le` / 定理 `lift_le`

English:
theorem lift_le
  given: {a b : Cardinal.{v}}
  statement: lift.{u} a <= lift.{u} b ↔ a <= b
  proof: liftInitialSeg.le_iff_le

@[simp]

中文:
定理 lift_le
  条件: {a b : Cardinal.{v}}
  结论: lift.{u} a <= lift.{u} b ↔ a <= b
  证明: liftInitialSeg.le_iff_le

@[simp]

Depends on / 依赖: le_iff_le, liftInitialSeg, liftInitialSeg.le_iff_le
-/
theorem lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} b ↔ a <= b :=
  liftInitialSeg.le_iff_le

@[simp]
/--
theorem `lift_lt` / 定理 `lift_lt`

English:
theorem lift_lt
  given: {a b : Cardinal.{u}}
  statement: lift.{v, u} a < lift.{v, u} b ↔ a < b
  proof: liftInitialSeg.lt_iff_lt

中文:
定理 lift_lt
  条件: {a b : Cardinal.{u}}
  结论: lift.{v, u} a < lift.{v, u} b ↔ a < b
  证明: liftInitialSeg.lt_iff_lt

Depends on / 依赖: liftInitialSeg, liftInitialSeg.lt_iff_lt, lt_iff_lt
-/
theorem lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v, u} b ↔ a < b :=
  liftInitialSeg.lt_iff_lt

/--
theorem `lift_strictMono` / 定理 `lift_strictMono`

English:
theorem lift_strictMono
  statement: StrictMono lift
  proof: fun _ _ => lift_lt.2

中文:
定理 lift_strictMono
  结论: StrictMono lift
  证明: fun _ _ => lift_lt.2

Depends on / 依赖: lift_lt
-/
theorem lift_strictMono : StrictMono lift := fun _ _ => lift_lt.2

/--
theorem `lift_monotone` / 定理 `lift_monotone`

English:
theorem lift_monotone
  statement: Monotone lift
  proof: lift_strictMono.monotone

@[simp]

中文:
定理 lift_monotone
  结论: Monotone lift
  证明: lift_strictMono.monotone

@[simp]

Depends on / 依赖: lift_strictMono, lift_strictMono.monotone, monotone
-/
theorem lift_monotone : Monotone lift :=
  lift_strictMono.monotone

@[simp]
/--
theorem `lift_min` / 定理 `lift_min`

English:
theorem lift_min
  given: {a b : Cardinal}
  statement: lift.{u, v} (min a b) = min (lift.{u, v} a) (lift.{u, v} b)
  proof: lift_monotone.map_min

@[simp]

中文:
定理 lift_min
  条件: {a b : Cardinal}
  结论: lift.{u, v} (min a b) = min (lift.{u, v} a) (lift.{u, v} b)
  证明: lift_monotone.map_min

@[simp]

Depends on / 依赖: lift_monotone, lift_monotone.map_min, map_min
-/
theorem lift_min {a b : Cardinal} : lift.{u, v} (min a b) = min (lift.{u, v} a) (lift.{u, v} b) :=
  lift_monotone.map_min

@[simp]
/--
theorem `lift_max` / 定理 `lift_max`

English:
theorem lift_max
  given: {a b : Cardinal}
  statement: lift.{u, v} (max a b) = max (lift.{u, v} a) (lift.{u, v} b)
  proof: lift_monotone.map_max

中文:
定理 lift_max
  条件: {a b : Cardinal}
  结论: lift.{u, v} (max a b) = max (lift.{u, v} a) (lift.{u, v} b)
  证明: lift_monotone.map_max

Depends on / 依赖: lift_monotone, lift_monotone.map_max, map_max
-/
theorem lift_max {a b : Cardinal} : lift.{u, v} (max a b) = max (lift.{u, v} a) (lift.{u, v} b) :=
  lift_monotone.map_max

-- This cannot be a `@[simp]` lemma because `simp` can't figure out the universes.
/--
theorem `lift_umax_eq` / 定理 `lift_umax_eq`

English:
theorem lift_umax_eq
  given: {a : Cardinal.{u}} {b : Cardinal.{v}}
  proof: by
  rw [← lift_lift.{v]; rw [w]; rw [u}]; rw [← lift_lift.{u]; rw [w]; rw [v}]; rw [lift_inj]

中文:
定理 lift_umax_eq
  条件: {a : Cardinal.{u}} {b : Cardinal.{v}}
  证明: by
  rw [← lift_lift.{v]; rw [w]; rw [u}]; rw [← lift_lift.{u]; rw [w]; rw [v}]; rw [lift_inj]

Depends on / 依赖: lift_inj, lift_lift
-/
theorem lift_umax_eq {a : Cardinal.{u}} {b : Cardinal.{v}} :
    lift.{max v w} a = lift.{max u w} b ↔ lift.{v} a = lift.{u} b := by
  rw [← lift_lift.{v]; rw [w]; rw [u}]; rw [← lift_lift.{u]; rw [w]; rw [v}]; rw [lift_inj]

/--
theorem `le_lift_iff` / 定理 `le_lift_iff`

English:
theorem le_lift_iff
  given: {a : Cardinal.{u}} {b : Cardinal.{max u v}}
  proof: liftInitialSeg.le_apply_iff

中文:
定理 le_lift_iff
  条件: {a : Cardinal.{u}} {b : Cardinal.{max u v}}
  证明: liftInitialSeg.le_apply_iff

Depends on / 依赖: le_apply_iff, liftInitialSeg, liftInitialSeg.le_apply_iff
-/
theorem le_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b <= lift.{v, u} a ↔ exists a' <= a, lift.{v, u} a' = b :=
  liftInitialSeg.le_apply_iff

/--
theorem `lt_lift_iff` / 定理 `lt_lift_iff`

English:
theorem lt_lift_iff
  given: {a : Cardinal.{u}} {b : Cardinal.{max u v}}
  proof: liftInitialSeg.lt_apply_iff

中文:
定理 lt_lift_iff
  条件: {a : Cardinal.{u}} {b : Cardinal.{max u v}}
  证明: liftInitialSeg.lt_apply_iff

Depends on / 依赖: liftInitialSeg, liftInitialSeg.lt_apply_iff, lt_apply_iff
-/
theorem lt_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b < lift.{v, u} a ↔ exists a' < a, lift.{v, u} a' = b :=
  liftInitialSeg.lt_apply_iff

/-! ### Basic cardinals -/

@[simp]
/--
theorem `lift_eq_zero` / 定理 `lift_eq_zero`

English:
theorem lift_eq_zero
  given: {a : Cardinal.{v}}
  statement: lift.{u} a = 0 ↔ a = 0
  proof: lift_injective.eq_iff' lift_zero

@[simp]

中文:
定理 lift_eq_zero
  条件: {a : Cardinal.{v}}
  结论: lift.{u} a = 0 ↔ a = 0
  证明: lift_injective.eq_iff' lift_zero

@[simp]

Depends on / 依赖: eq_iff, lift_injective, lift_injective.eq_iff, lift_zero
-/
theorem lift_eq_zero {a : Cardinal.{v}} : lift.{u} a = 0 ↔ a = 0 :=
  lift_injective.eq_iff' lift_zero

@[simp]
/--
theorem `mk_fintype` / 定理 `mk_fintype`

English:
theorem mk_fintype
  given: (α : Type u) [h : Fintype α]
  statement: #α = Fintype.card α
  proof: mk_congr (Fintype.equivOfCardEq (by simp))

中文:
定理 mk_fintype
  条件: (α : 类型u) [h : Fintype α]
  结论: #α = Fintype.card α
  证明: mk_congr (Fintype.equivOfCardEq (by simp))

Depends on / 依赖: Fintype, Fintype.equivOfCardEq, equivOfCardEq, mk_congr
-/
theorem mk_fintype (α : Type u) [h : Fintype α] : #α = Fintype.card α :=
  mk_congr (Fintype.equivOfCardEq (by simp))

set_option backward.privateInPublic true in
/--
theorem `cast_succ` / 定理 `cast_succ`

English:
theorem cast_succ
  given: (n : Nat)
  statement: ((n + 1 : Nat) : Cardinal.{u}) = n + 1
  proof: by
  change #(ULift.{u} _) = #(ULift.{u} _) + 1
  rw [← mk_option]
  simp

中文:
定理 cast_succ
  条件: (n : 自然数)
  结论: ((n + 1 : 自然数) : Cardinal.{u}) = n + 1
  证明: by
  change #(ULift.{u} _) = #(ULift.{u} _) + 1
  rw [← mk_option]
  simp
-/
private theorem cast_succ (n : Nat) : ((n + 1 : Nat) : Cardinal.{u}) = n + 1 := by
  change #(ULift.{u} _) = #(ULift.{u} _) + 1
  rw [← mk_option]
  simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `commSemiring` / 实例 `commSemiring`

English:
instance commSemiring
  signature: : CommSemiring Cardinal.{u} where
  body: inductionOn a fun α => mk_congr Equiv.emptySum _ α
add_zero a := inductionOn a fun α => mk_congr Equiv.sumEmpty α _
add_assoc a b c := inductionOn₃ a b c fun α β γ => mk_congr Equiv.sumAssoc α β γ
add_comm a b := inductionOn₂ a b fun α β => mk_congr Equiv.sumComm α β
  zero_mul a := inductionOn a fu

中文:
实例 commSemiring
  签名: : CommSemiring Cardinal.{u} where
  定义体: inductionOn a fun α => mk_congr Equiv.emptySum _ α
add_zero a := inductionOn a fun α => mk_congr Equiv.sumEmpty α _
add_assoc a b c := inductionOn₃ a b c fun α β γ => mk_congr Equiv.sumAssoc α β γ
add_comm a b := inductionOn₂ a b fun α β => mk_congr Equiv.sumComm α β
  zero_mul a := inductionOn a fu

Depends on / 依赖: Equiv.emptySum, emptySum, inductionOn, mk_congr
-/
instance commSemiring : CommSemiring Cardinal.{u} where
zero_add a := inductionOn a fun α => mk_congr Equiv.emptySum _ α
add_zero a := inductionOn a fun α => mk_congr Equiv.sumEmpty α _
add_assoc a b c := inductionOn₃ a b c fun α β γ => mk_congr Equiv.sumAssoc α β γ
add_comm a b := inductionOn₂ a b fun α β => mk_congr Equiv.sumComm α β
  zero_mul a := inductionOn a fun _ => mk_eq_zero _
  mul_zero a := inductionOn a fun _ => mk_eq_zero _
one_mul a := inductionOn a fun α => mk_congr Equiv.uniqueProd α _
mul_one a := inductionOn a fun α => mk_congr Equiv.prodUnique α _
mul_assoc a b c := inductionOn₃ a b c fun α β γ => mk_congr Equiv.prodAssoc α β γ
mul_comm a b := inductionOn₂ a b fun α β => mk_congr Equiv.prodComm α β
left_distrib a b c := inductionOn₃ a b c fun α β γ => mk_congr Equiv.prodSumDistrib α β γ
right_distrib a b c := inductionOn₃ a b c fun α β γ => mk_congr Equiv.sumProdDistrib α β γ
  nsmul := nsmulRec
  npow n c := c ^ (n : Cardinal)
  npow_zero := power_zero
  npow_succ n c := by simp_rw [HPow.hPow, Pow.pow]; rw [cast_succ, power_add, power_one]
  natCast n := lift #(Fin n)
  natCast_zero := rfl
  natCast_succ n := cast_succ n

/--
theorem `mk_bool` / 定理 `mk_bool`

English:
theorem mk_bool
  statement: #Bool = 2
  proof: by simp

中文:
定理 mk_bool
  结论: #布尔 = 2
  证明: by simp
-/
theorem mk_bool : #Bool = 2 := by simp

/--
theorem `mk_Prop` / 定理 `mk_Prop`

English:
theorem mk_Prop
  statement: #Prop = 2
  proof: by simp

中文:
定理 mk_Prop
  结论: #命题 = 2
  证明: by simp
-/
theorem mk_Prop : #Prop = 2 := by simp

/--
theorem `power_mul` / 定理 `power_mul`

English:
theorem power_mul
  given: {a b c : Cardinal}
  statement: a ^ (b * c) = (a ^ b) ^ c
  proof: by
  rw [mul_comm b c]
exact inductionOn₃ a b c fun α β γ => mk_congr Equiv.curry γ β α

@[simp, norm_cast]

中文:
定理 power_mul
  条件: {a b c : Cardinal}
  结论: a ^ (b * c) = (a ^ b) ^ c
  证明: by
  rw [mul_comm b c]
exact inductionOn₃ a b c fun α β γ => mk_congr Equiv.curry γ β α

@[simp, norm_cast]

Depends on / 依赖: Equiv.curry, mk_congr, mul_comm
-/
theorem power_mul {a b c : Cardinal} : a ^ (b * c) = (a ^ b) ^ c := by
  rw [mul_comm b c]
exact inductionOn₃ a b c fun α β γ => mk_congr Equiv.curry γ β α

@[simp, norm_cast]
/--
theorem `power_natCast` / 定理 `power_natCast`

English:
theorem power_natCast
  given: (a : Cardinal.{u}) (n : Nat)
  statement: a ^ (↑n : Cardinal.{u}) = a ^ n
  proof: rfl

@[simp]

中文:
定理 power_natCast
  条件: (a : Cardinal.{u}) (n : 自然数)
  结论: a ^ (↑n : Cardinal.{u}) = a ^ n
  证明: rfl

@[simp]
-/
theorem power_natCast (a : Cardinal.{u}) (n : Nat) : a ^ (↑n : Cardinal.{u}) = a ^ n :=
  rfl

@[simp]
/--
theorem `lift_eq_one` / 定理 `lift_eq_one`

English:
theorem lift_eq_one
  given: {a : Cardinal.{v}}
  statement: lift.{u} a = 1 ↔ a = 1
  proof: lift_injective.eq_iff' lift_one

@[simp]

中文:
定理 lift_eq_one
  条件: {a : Cardinal.{v}}
  结论: lift.{u} a = 1 ↔ a = 1
  证明: lift_injective.eq_iff' lift_one

@[simp]

Depends on / 依赖: eq_iff, lift_injective, lift_injective.eq_iff, lift_one
-/
theorem lift_eq_one {a : Cardinal.{v}} : lift.{u} a = 1 ↔ a = 1 :=
  lift_injective.eq_iff' lift_one

@[simp]
/--
theorem `lift_mul` / 定理 `lift_mul`

English:
theorem lift_mul
  given: (a b : Cardinal.{u})
  statement: lift.{v} (a * b) = lift.{v} a * lift.{v} b
  proof: inductionOn₂ a b fun _ _ =>
mk_congr Equiv.ulift.trans (Equiv.prodCongr Equiv.ulift Equiv.ulift).symm

中文:
定理 lift_mul
  条件: (a b : Cardinal.{u})
  结论: lift.{v} (a * b) = lift.{v} a * lift.{v} b
  证明: inductionOn₂ a b fun _ _ =>
mk_congr Equiv.ulift.trans (Equiv.prodCongr Equiv.ulift Equiv.ulift).symm

Depends on / 依赖: Equiv.prodCongr, Equiv.ulift, Equiv.ulift.trans, mk_congr, prodCongr
-/
theorem lift_mul (a b : Cardinal.{u}) : lift.{v} (a * b) = lift.{v} a * lift.{v} b :=
  inductionOn₂ a b fun _ _ =>
mk_congr Equiv.ulift.trans (Equiv.prodCongr Equiv.ulift Equiv.ulift).symm

/--
theorem `lift_two` / 定理 `lift_two`

English:
theorem lift_two
  statement: lift.{u, v} 2 = 2
  proof: by simp [← one_add_one_eq_two]

@[simp]

中文:
定理 lift_two
  结论: lift.{u, v} 2 = 2
  证明: by simp [← one_add_one_eq_two]

@[simp]

Depends on / 依赖: one_add_one_eq_two
-/
theorem lift_two : lift.{u, v} 2 = 2 := by simp [← one_add_one_eq_two]

@[simp]
/--
theorem `mk_set` / 定理 `mk_set`

English:
theorem mk_set
  given: {α : Type u}
  statement: #(Set α) = 2 ^ #α
  proof: by
  simp [← mk_congr (Equiv.ofBijective _ Set.ofPred_bijective), ← one_add_one_eq_two]

中文:
定理 mk_set
  条件: {α : 类型u}
  结论: #(Set α) = 2 ^ #α
  证明: by
  simp [← mk_congr (Equiv.ofBijective _ Set.ofPred_bijective), ← one_add_one_eq_two]

Depends on / 依赖: Equiv.ofBijective, Set.ofPred_bijective, mk_congr, ofBijective, ofPred_bijective, one_add_one_eq_two
-/
theorem mk_set {α : Type u} : #(Set α) = 2 ^ #α := by
  simp [← mk_congr (Equiv.ofBijective _ Set.ofPred_bijective), ← one_add_one_eq_two]

/-- A variant of `Cardinal.mk_set` expressed in terms of a `Set` instead of a `Type`. -/
@[simp]
/--
theorem `mk_powerset` / 定理 `mk_powerset`

English:
theorem mk_powerset
  given: {α : Type u} (s : Set α)
  statement: #(↥(𝒫 s)) = 2 ^ #(↥s)
  proof: (mk_congr (Equiv.Set.powerset s)).trans mk_set

中文:
定理 mk_powerset
  条件: {α : 类型u} (s : Set α)
  结论: #(↥(𝒫 s)) = 2 ^ #(↥s)
  证明: (mk_congr (Equiv.Set.powerset s)).trans mk_set

Depends on / 依赖: Equiv.Set.powerset, mk_congr, mk_set, powerset
-/
theorem mk_powerset {α : Type u} (s : Set α) : #(↥(𝒫 s)) = 2 ^ #(↥s) :=
  (mk_congr (Equiv.Set.powerset s)).trans mk_set

/--
theorem `lift_two_power` / 定理 `lift_two_power`

English:
theorem lift_two_power
  given: (a : Cardinal)
  statement: lift.{v} (2 ^ a) = 2 ^ lift.{v} a
  proof: by
  simp [← one_add_one_eq_two]

中文:
定理 lift_two_power
  条件: (a : Cardinal)
  结论: lift.{v} (2 ^ a) = 2 ^ lift.{v} a
  证明: by
  simp [← one_add_one_eq_two]

Depends on / 依赖: one_add_one_eq_two
-/
theorem lift_two_power (a : Cardinal) : lift.{v} (2 ^ a) = 2 ^ lift.{v} a := by
  simp [← one_add_one_eq_two]


/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: : OrderBot Cardinal.{u} where
  body: 0
  bot_le := by rintro ⟨α⟩; exact ⟨Embedding.ofIsEmpty⟩

中文:
实例 orderBot
  签名: : OrderBot Cardinal.{u} where
  定义体: 0
  bot_le := by rintro ⟨α⟩; exact ⟨Embedding.ofIsEmpty⟩
-/
instance orderBot : OrderBot Cardinal.{u} where
  bot := 0
  bot_le := by rintro ⟨α⟩; exact ⟨Embedding.ofIsEmpty⟩

/--
theorem `add_le_add'` / 定理 `add_le_add'`

English:
theorem add_le_add'
  statement: forall {a b c d : Cardinal}, a <= b -> c <= d -> a + c <= b + d
  proof: by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨δ⟩ ⟨e₁⟩ ⟨e₂⟩; exact ⟨e₁.sumMap e₂⟩

中文:
定理 add_le_add'
  结论: 对任意 {a b c d : Cardinal}, a <= b -> c <= d -> a + c <= b + d
  证明: by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨δ⟩ ⟨e₁⟩ ⟨e₂⟩; exact ⟨e₁.sumMap e₂⟩
-/
private theorem add_le_add' : forall {a b c d : Cardinal}, a <= b -> c <= d -> a + c <= b + d := by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨δ⟩ ⟨e₁⟩ ⟨e₂⟩; exact ⟨e₁.sumMap e₂⟩

/--
Instance `addLeftMono` / 实例 `addLeftMono`

English:
instance addLeftMono
  signature: : AddLeftMono Cardinal
  body: ⟨fun _ _ _ => add_le_add' le_rfl⟩

中文:
实例 addLeftMono
  签名: : AddLeftMono Cardinal
  定义体: ⟨fun _ _ _ => add_le_add' le_rfl⟩

Depends on / 依赖: add_le_add, le_rfl
-/
instance addLeftMono : AddLeftMono Cardinal :=
  ⟨fun _ _ _ => add_le_add' le_rfl⟩

/--
Instance `addRightMono` / 实例 `addRightMono`

English:
instance addRightMono
  signature: : AddRightMono Cardinal
  body: ⟨fun _ _ _ h => add_le_add' h le_rfl⟩

中文:
实例 addRightMono
  签名: : AddRightMono Cardinal
  定义体: ⟨fun _ _ _ h => add_le_add' h le_rfl⟩

Depends on / 依赖: add_le_add, le_rfl
-/
instance addRightMono : AddRightMono Cardinal :=
  ⟨fun _ _ _ h => add_le_add' h le_rfl⟩

/--
Instance `canonicallyOrderedAdd` / 实例 `canonicallyOrderedAdd`

English:
instance canonicallyOrderedAdd
  signature: : CanonicallyOrderedAdd Cardinal.{u} where
  body: inductionOn₂ a b fun α β ⟨⟨f, hf⟩⟩ =>
      have : α oplus ((range f)ᶜ : Set β) ≃ β := by
        classical
exact (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl _)).trans
          Equiv.Set.sumCompl (range f)
      ⟨#(↥(range f)ᶜ), mk_congr this.symm⟩
le_self_add a b := (add_zero a).ge.trans 

中文:
实例 canonicallyOrderedAdd
  签名: : CanonicallyOrderedAdd Cardinal.{u} where
  定义体: inductionOn₂ a b fun α β ⟨⟨f, hf⟩⟩ =>
      have : α oplus ((range f)ᶜ : Set β) ≃ β := by
        classical
exact (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl _)).trans
          Equiv.Set.sumCompl (range f)
      ⟨#(↥(range f)ᶜ), mk_congr this.symm⟩
le_self_add a b := (add_zero a).ge.trans 

Depends on / 依赖: Equiv.Set.sumCompl, Equiv.ofInjective, Equiv.refl, Equiv.sumCongr, add_left_mono, add_right_mono, add_zero, bot_le, classical, ge.trans, le_add_self, le_self_add, mk_congr, ofInjective, sumCompl, sumCongr, this.symm, zero_add
-/
instance canonicallyOrderedAdd : CanonicallyOrderedAdd Cardinal.{u} where
  exists_add_of_le {a b} :=
    inductionOn₂ a b fun α β ⟨⟨f, hf⟩⟩ =>
      have : α oplus ((range f)ᶜ : Set β) ≃ β := by
        classical
exact (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl _)).trans
          Equiv.Set.sumCompl (range f)
      ⟨#(↥(range f)ᶜ), mk_congr this.symm⟩
le_self_add a b := (add_zero a).ge.trans add_right_mono bot_le
le_add_self a b := (zero_add a).ge.trans add_left_mono bot_le

@[deprecated zero_le (since := "2026-04-17")]
/--
theorem `zero_le` / 定理 `zero_le`

English:
theorem zero_le
  given: (a : Cardinal)
  statement: 0 <= a
  proof: zero_le

中文:
定理 zero_le
  条件: (a : Cardinal)
  结论: 0 <= a
  证明: zero_le
-/
protected theorem zero_le (a : Cardinal) : 0 <= a := zero_le

/--
Instance `isOrderedRing` / 实例 `isOrderedRing`

English:
instance isOrderedRing
  signature: : IsOrderedRing Cardinal.{u}
  body: CanonicallyOrderedAdd.toIsOrderedRing

中文:
实例 isOrderedRing
  签名: : IsOrderedRing Cardinal.{u}
  定义体: CanonicallyOrderedAdd.toIsOrderedRing

Depends on / 依赖: CanonicallyOrderedAdd, CanonicallyOrderedAdd.toIsOrderedRing, toIsOrderedRing
-/
instance isOrderedRing : IsOrderedRing Cardinal.{u} :=
  CanonicallyOrderedAdd.toIsOrderedRing

/--
Instance `noZeroDivisors` / 实例 `noZeroDivisors`

English:
instance noZeroDivisors
  signature: : NoZeroDivisors Cardinal.{u} where
  body: fun {a b} =>
    inductionOn₂ a b fun α β => by
      simpa only [mul_def, mk_eq_zero_iff, isEmpty_prod] using id

中文:
实例 noZeroDivisors
  签名: : NoZeroDivisors Cardinal.{u} where
  定义体: fun {a b} =>
    inductionOn₂ a b fun α β => by
      simpa only [mul_def, mk_eq_zero_iff, isEmpty_prod] using id
-/
instance noZeroDivisors : NoZeroDivisors Cardinal.{u} where
  eq_zero_or_eq_zero_of_mul_eq_zero := fun {a b} =>
    inductionOn₂ a b fun α β => by
      simpa only [mul_def, mk_eq_zero_iff, isEmpty_prod] using id

-- Computable instance to prevent a non-computable one being found via the one above
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommMonoidWithZero Cardinal.{u}
  body: { Cardinal.commSemiring with }

中文:
实例 :
  签名: CommMonoidWithZero Cardinal.{u}
  定义体: { Cardinal.commSemiring with }

Depends on / 依赖: Cardinal, Cardinal.commSemiring, commSemiring
-/
instance : CommMonoidWithZero Cardinal.{u} :=
  { Cardinal.commSemiring with }

-- Computable instance to prevent a non-computable one being found via the one above
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommMonoid Cardinal.{u}
  body: { Cardinal.commSemiring with }

中文:
实例 :
  签名: CommMonoid Cardinal.{u}
  定义体: { Cardinal.commSemiring with }

Depends on / 依赖: Cardinal, Cardinal.commSemiring, commSemiring
-/
instance : CommMonoid Cardinal.{u} :=
  { Cardinal.commSemiring with }

/--
theorem `zero_power_le` / 定理 `zero_power_le`

English:
theorem zero_power_le
  given: (c : Cardinal.{u})
  statement: (0 : Cardinal.{u}) ^ c <= 1
  proof: by
  by_cases h : c = 0
  · rw [h, power_zero]
  · rw [zero_power h]
    apply zero_le

中文:
定理 zero_power_le
  条件: (c : Cardinal.{u})
  结论: (0 : Cardinal.{u}) ^ c <= 1
  证明: by
  by_cases h : c = 0
  · rw [h, power_zero]
  · rw [zero_power h]
    apply zero_le

Depends on / 依赖: power_zero, zero_le, zero_power
-/
theorem zero_power_le (c : Cardinal.{u}) : (0 : Cardinal.{u}) ^ c <= 1 := by
  by_cases h : c = 0
  · rw [h, power_zero]
  · rw [zero_power h]
    apply zero_le

/--
theorem `power_le_power_left` / 定理 `power_le_power_left`

English:
theorem power_le_power_left
  statement: forall {a b c : Cardinal}, a != 0 -> b <= c -> a ^ b <= a ^ c
  proof: by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ hα ⟨e⟩
  let ⟨a⟩ := mk_ne_zero_iff.1 hα
  exact ⟨@Function.Embedding.arrowCongrLeft _ _ _ ⟨a⟩ e⟩

中文:
定理 power_le_power_left
  结论: 对任意 {a b c : Cardinal}, a != 0 -> b <= c -> a ^ b <= a ^ c
  证明: by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ hα ⟨e⟩
  let ⟨a⟩ := mk_ne_zero_iff.1 hα
  exact ⟨@Function.Embedding.arrowCongrLeft _ _ _ ⟨a⟩ e⟩

Depends on / 依赖: Embedding, Function, Function.Embedding.arrowCongrLeft, arrowCongrLeft, mk_ne_zero_iff
-/
theorem power_le_power_left : forall {a b c : Cardinal}, a != 0 -> b <= c -> a ^ b <= a ^ c := by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ hα ⟨e⟩
  let ⟨a⟩ := mk_ne_zero_iff.1 hα
  exact ⟨@Function.Embedding.arrowCongrLeft _ _ _ ⟨a⟩ e⟩

/--
theorem `self_le_power` / 定理 `self_le_power`

English:
theorem self_le_power
  given: (a : Cardinal) {b : Cardinal} (hb : 1 <= b)
  statement: a <= a ^ b
  proof: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact zero_le
  · convert! power_le_power_left ha hb
    exact (power_one a).symm

中文:
定理 self_le_power
  条件: (a : Cardinal) {b : Cardinal} (hb : 1 <= b)
  结论: a <= a ^ b
  证明: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact zero_le
  · convert! power_le_power_left ha hb
    exact (power_one a).symm

Depends on / 依赖: convert, eq_or_ne, power_le_power_left, power_one, zero_le
-/
theorem self_le_power (a : Cardinal) {b : Cardinal} (hb : 1 <= b) : a <= a ^ b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact zero_le
  · convert! power_le_power_left ha hb
    exact (power_one a).symm

/--
theorem `cantor` / 定理 `cantor`

English:
theorem cantor
  given: (a : Cardinal.{u})
  statement: a < 2 ^ a
  proof: by
  induction a using Cardinal.inductionOn with | _ α
  rw [← mk_set]
  refine ⟨⟨⟨singleton, fun a b => singleton_eq_singleton_iff.1⟩⟩, ?_⟩
  rintro ⟨⟨f, hf⟩⟩
  exact cantor_injective f hf

中文:
定理 cantor
  条件: (a : Cardinal.{u})
  结论: a < 2 ^ a
  证明: by
  induction a using Cardinal.inductionOn with | _ α
  rw [← mk_set]
  refine ⟨⟨⟨singleton, fun a b => singleton_eq_singleton_iff.1⟩⟩, ?_⟩
  rintro ⟨⟨f, hf⟩⟩
  exact cantor_injective f hf

Depends on / 依赖: Cardinal, Cardinal.inductionOn, cantor_injective, inductionOn, mk_set, singleton, singleton_eq_singleton_iff
-/
theorem cantor (a : Cardinal.{u}) : a < 2 ^ a := by
  induction a using Cardinal.inductionOn with | _ α
  rw [← mk_set]
  refine ⟨⟨⟨singleton, fun a b => singleton_eq_singleton_iff.1⟩⟩, ?_⟩
  rintro ⟨⟨f, hf⟩⟩
  exact cantor_injective f hf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoMaxOrder Cardinal.{u}
  body: ⟨_, cantor a⟩

中文:
实例 :
  签名: NoMaxOrder Cardinal.{u}
  定义体: ⟨_, cantor a⟩

Depends on / 依赖: cantor
-/
instance : NoMaxOrder Cardinal.{u} where exists_gt a := ⟨_, cantor a⟩

-- short-circuit type class inference
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribLattice Cardinal.{u}
  body: inferInstance

中文:
实例 :
  签名: DistribLattice Cardinal.{u}
  定义体: inferInstance
-/
instance : DistribLattice Cardinal.{u} := inferInstance

/--
theorem `power_le_max_power_one` / 定理 `power_le_max_power_one`

English:
theorem power_le_max_power_one
  given: {a b c : Cardinal} (h : b <= c)
  statement: a ^ b <= max (a ^ c) 1
  proof: by
  by_cases ha : a = 0
  · simp [ha, zero_power_le]
  · exact (power_le_power_left ha h).trans (le_max_left _ _)

中文:
定理 power_le_max_power_one
  条件: {a b c : Cardinal} (h : b <= c)
  结论: a ^ b <= max (a ^ c) 1
  证明: by
  by_cases ha : a = 0
  · simp [ha, zero_power_le]
  · exact (power_le_power_left ha h).trans (le_max_left _ _)

Depends on / 依赖: le_max_left, power_le_power_left, zero_power_le
-/
theorem power_le_max_power_one {a b c : Cardinal} (h : b <= c) : a ^ b <= max (a ^ c) 1 := by
  by_cases ha : a = 0
  · simp [ha, zero_power_le]
  · exact (power_le_power_left ha h).trans (le_max_left _ _)

/--
theorem `power_le_power_right` / 定理 `power_le_power_right`

English:
theorem power_le_power_right
  given: {a b c : Cardinal}
  statement: a <= b -> a ^ c <= b ^ c
  proof: inductionOn₃ a b c fun _ _ _ ⟨e⟩ => ⟨Embedding.arrowCongrRight e⟩

中文:
定理 power_le_power_right
  条件: {a b c : Cardinal}
  结论: a <= b -> a ^ c <= b ^ c
  证明: inductionOn₃ a b c fun _ _ _ ⟨e⟩ => ⟨Embedding.arrowCongrRight e⟩

Depends on / 依赖: Embedding, Embedding.arrowCongrRight, arrowCongrRight
-/
theorem power_le_power_right {a b c : Cardinal} : a <= b -> a ^ c <= b ^ c :=
  inductionOn₃ a b c fun _ _ _ ⟨e⟩ => ⟨Embedding.arrowCongrRight e⟩

/--
theorem `power_pos` / 定理 `power_pos`

English:
theorem power_pos
  given: {a : Cardinal} (b : Cardinal) (ha : 0 < a)
  statement: 0 < a ^ b
  proof: (power_ne_zero _ ha.ne').bot_lt

中文:
定理 power_pos
  条件: {a : Cardinal} (b : Cardinal) (ha : 0 < a)
  结论: 0 < a ^ b
  证明: (power_ne_zero _ ha.ne').bot_lt

Depends on / 依赖: bot_lt, ha.ne, power_ne_zero
-/
theorem power_pos {a : Cardinal} (b : Cardinal) (ha : 0 < a) : 0 < a ^ b :=
  (power_ne_zero _ ha.ne').bot_lt

/--
theorem `lt_wf` / 定理 `lt_wf`

English:
theorem lt_wf
  statement: @WellFounded Cardinal.{u} (· < ·)
  proof: ⟨fun a =>
    by_contradiction fun h => by
      let ι := { c : Cardinal // ¬Acc (· < ·) c }
      let f : ι -> Cardinal := Subtype.val
      have hι : Nonempty ι := ⟨⟨_, h⟩⟩
      obtain ⟨⟨c : Cardinal, hc : ¬Acc (· < ·) c⟩, ⟨h_1 : forall j, (f ⟨c, hc⟩).out ↪ (f j).out⟩⟩ :=
        Embedding.min_in

中文:
定理 lt_wf
  结论: @WellFounded Cardinal.{u} (· < ·)
  证明: ⟨fun a =>
    by_contradiction fun h => by
      let ι := { c : Cardinal // ¬Acc (· < ·) c }
      let f : ι -> Cardinal := Subtype.val
      have hι : Nonempty ι := ⟨⟨_, h⟩⟩
      obtain ⟨⟨c : Cardinal, hc : ¬Acc (· < ·) c⟩, ⟨h_1 : forall j, (f ⟨c, hc⟩).out ↪ (f j).out⟩⟩ :=
        Embedding.min_in
-/
protected theorem lt_wf : @WellFounded Cardinal.{u} (· < ·) :=
  ⟨fun a =>
    by_contradiction fun h => by
      let ι := { c : Cardinal // ¬Acc (· < ·) c }
      let f : ι -> Cardinal := Subtype.val
      have hι : Nonempty ι := ⟨⟨_, h⟩⟩
      obtain ⟨⟨c : Cardinal, hc : ¬Acc (· < ·) c⟩, ⟨h_1 : forall j, (f ⟨c, hc⟩).out ↪ (f j).out⟩⟩ :=
        Embedding.min_injective fun i => (f i).out
      refine hc (Acc.intro _ fun j h' => by_contradiction fun hj => h'.2 ?_)
      have : #_ <= #_ := ⟨h_1 ⟨j, hj⟩⟩
      simpa only [mk_out] using this⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WellFoundedRelation Cardinal.{u}
  body: ⟨(· < ·), Cardinal.lt_wf⟩

中文:
实例 :
  签名: WellFoundedRelation Cardinal.{u}
  定义体: ⟨(· < ·), Cardinal.lt_wf⟩

Depends on / 依赖: Cardinal, Cardinal.lt_wf, lt_wf
-/
instance : WellFoundedRelation Cardinal.{u} :=
  ⟨(· < ·), Cardinal.lt_wf⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WellFoundedLT Cardinal.{u}
  body: ⟨Cardinal.lt_wf⟩

中文:
实例 :
  签名: WellFoundedLT Cardinal.{u}
  定义体: ⟨Cardinal.lt_wf⟩

Depends on / 依赖: Cardinal, Cardinal.lt_wf, lt_wf
-/
instance : WellFoundedLT Cardinal.{u} :=
  ⟨Cardinal.lt_wf⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConditionallyCompleteLinearOrderBot Cardinal
  body: WellFoundedLT.conditionallyCompleteLinearOrderBot _

@[simp]

中文:
实例 :
  签名: ConditionallyCompleteLinearOrderBot Cardinal
  定义体: WellFoundedLT.conditionallyCompleteLinearOrderBot _

@[simp]

Depends on / 依赖: WellFoundedLT, WellFoundedLT.conditionallyCompleteLinearOrderBot, conditionallyCompleteLinearOrderBot
-/
instance : ConditionallyCompleteLinearOrderBot Cardinal :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

@[simp]
/--
theorem `sInf_empty` / 定理 `sInf_empty`

English:
theorem sInf_empty
  statement: sInf (∅ : Set Cardinal.{u}) = 0
  proof: dif_neg Set.not_nonempty_empty

中文:
定理 sInf_empty
  结论: sInf (∅ : Set Cardinal.{u}) = 0
  证明: dif_neg Set.not_nonempty_empty

Depends on / 依赖: Set.not_nonempty_empty, dif_neg, not_nonempty_empty
-/
theorem sInf_empty : sInf (∅ : Set Cardinal.{u}) = 0 :=
  dif_neg Set.not_nonempty_empty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SuccOrder Cardinal
  body: .ofLinearWellFoundedLT _

@[deprecated Order.succ_eq_csInf (since := "2026-03-21")]

中文:
实例 :
  签名: SuccOrder Cardinal
  定义体: .ofLinearWellFoundedLT _

@[deprecated Order.succ_eq_csInf (since := "2026-03-21")]
-/
@[no_expose] instance : SuccOrder Cardinal := .ofLinearWellFoundedLT _

@[deprecated Order.succ_eq_csInf (since := "2026-03-21")]
/--
theorem `succ_def` / 定理 `succ_def`

English:
theorem succ_def
  given: (c : Cardinal)
  statement: succ c = sInf { c' | c < c' }
  proof: Order.succ_eq_csInf c

中文:
定理 succ_def
  条件: (c : Cardinal)
  结论: succ c = sInf { c' | c < c' }
  证明: Order.succ_eq_csInf c

Depends on / 依赖: Order.succ_eq_csInf, succ_eq_csInf
-/
theorem succ_def (c : Cardinal) : succ c = sInf { c' | c < c' } :=
  Order.succ_eq_csInf c

/--
theorem `succ_pos` / 定理 `succ_pos`

English:
theorem succ_pos
  statement: forall c : Cardinal, 0 < succ c
  proof: by simp

@[simp]

中文:
定理 succ_pos
  结论: 对任意 c : Cardinal, 0 < succ c
  证明: by simp

@[simp]
-/
theorem succ_pos : forall c : Cardinal, 0 < succ c := by simp

@[simp]
/--
theorem `succ_ne_zero` / 定理 `succ_ne_zero`

English:
theorem succ_ne_zero
  given: (c : Cardinal)
  statement: succ c != 0
  proof: (succ_pos _).ne'

中文:
定理 succ_ne_zero
  条件: (c : Cardinal)
  结论: succ c != 0
  证明: (succ_pos _).ne'

Depends on / 依赖: succ_pos
-/
theorem succ_ne_zero (c : Cardinal) : succ c != 0 :=
  (succ_pos _).ne'

/--
theorem `add_one_le_of_lt` / 定理 `add_one_le_of_lt`

English:
theorem add_one_le_of_lt
  given: {a b : Cardinal} (h : a < b)
  statement: a + 1 <= b
  proof: by
  induction a, b using Cardinal.inductionOn₂ with | mk α β
  obtain ⟨f⟩ := h.le
  have hf : ¬Surjective f := fun hn => h.not_ge (mk_le_of_surjective hn)
  rw [Surjective]; rw [not_forall] at hf
  obtain ⟨b, hb⟩ := hf
  rw [← mk_option]
  exact (f.optionElim b hb).cardinal_le

@[deprecated add_one

中文:
定理 add_one_le_of_lt
  条件: {a b : Cardinal} (h : a < b)
  结论: a + 1 <= b
  证明: by
  induction a, b using Cardinal.inductionOn₂ with | mk α β
  obtain ⟨f⟩ := h.le
  have hf : ¬Surjective f := fun hn => h.not_ge (mk_le_of_surjective hn)
  rw [Surjective]; rw [not_forall] at hf
  obtain ⟨b, hb⟩ := hf
  rw [← mk_option]
  exact (f.optionElim b hb).cardinal_le

@[deprecated add_one

Depends on / 依赖: Cardinal, Cardinal.inductionOn, Surjective, cardinal_le, f.optionElim, h.le, h.not_ge, mk_le_of_surjective, mk_option, not_forall, not_ge, optionElim
-/
theorem add_one_le_of_lt {a b : Cardinal} (h : a < b) : a + 1 <= b := by
  induction a, b using Cardinal.inductionOn₂ with | mk α β
  obtain ⟨f⟩ := h.le
  have hf : ¬Surjective f := fun hn => h.not_ge (mk_le_of_surjective hn)
  rw [Surjective]; rw [not_forall] at hf
  obtain ⟨b, hb⟩ := hf
  rw [← mk_option]
  exact (f.optionElim b hb).cardinal_le

@[deprecated add_one_le_of_lt (since := "2026-03-21")]
/--
theorem `add_one_le_succ` / 定理 `add_one_le_succ`

English:
theorem add_one_le_succ
  given: (c : Cardinal)
  statement: c + 1 <= succ c
  proof: add_one_le_of_lt (lt_succ c)

@[simp]

中文:
定理 add_one_le_succ
  条件: (c : Cardinal)
  结论: c + 1 <= succ c
  证明: add_one_le_of_lt (lt_succ c)

@[simp]

Depends on / 依赖: add_one_le_of_lt, lt_succ
-/
theorem add_one_le_succ (c : Cardinal) : c + 1 <= succ c :=
  add_one_le_of_lt (lt_succ c)

@[simp]
/--
theorem `lift_succ` / 定理 `lift_succ`

English:
theorem lift_succ
  given: (a)
  statement: lift.{v, u} (succ a) = succ (lift.{v, u} a)
  proof: by
  apply (succ_le_of_lt <| lift_lt.2 <| lt_succ a).antisymm'
  by_contra! h
  rcases lt_lift_iff.1 h with ⟨b, h, hb⟩
  rw [lt_succ_iff]; rw [← lift_le]; rw [hb] at h
  exact h.not_gt (lt_succ _)

中文:
定理 lift_succ
  条件: (a)
  结论: lift.{v, u} (succ a) = succ (lift.{v, u} a)
  证明: by
  apply (succ_le_of_lt <| lift_lt.2 <| lt_succ a).antisymm'
  by_contra! h
  rcases lt_lift_iff.1 h with ⟨b, h, hb⟩
  rw [lt_succ_iff]; rw [← lift_le]; rw [hb] at h
  exact h.not_gt (lt_succ _)

Depends on / 依赖: antisymm, h.not_gt, lift_le, lift_lt, lt_lift_iff, lt_succ, lt_succ_iff, not_gt, succ_le_of_lt
-/
theorem lift_succ (a) : lift.{v, u} (succ a) = succ (lift.{v, u} a) := by
  apply (succ_le_of_lt <| lift_lt.2 <| lt_succ a).antisymm'
  by_contra! h
  rcases lt_lift_iff.1 h with ⟨b, h, hb⟩
  rw [lt_succ_iff]; rw [← lift_le]; rw [hb] at h
  exact h.not_gt (lt_succ _)


/--
theorem `ne_zero_of_isSuccLimit` / 定理 `ne_zero_of_isSuccLimit`

English:
theorem ne_zero_of_isSuccLimit
  given: {c} (h : IsSuccLimit c)
  statement: c != 0
  proof: h.ne_bot

中文:
定理 ne_zero_of_isSuccLimit
  条件: {c} (h : IsSuccLimit c)
  结论: c != 0
  证明: h.ne_bot

Depends on / 依赖: h.ne_bot, ne_bot
-/
theorem ne_zero_of_isSuccLimit {c} (h : IsSuccLimit c) : c != 0 :=
  h.ne_bot

/--
theorem `isSuccPrelimit_zero` / 定理 `isSuccPrelimit_zero`

English:
theorem isSuccPrelimit_zero
  statement: IsSuccPrelimit (0 : Cardinal)
  proof: isSuccPrelimit_bot

中文:
定理 isSuccPrelimit_zero
  结论: IsSuccPrelimit (0 : Cardinal)
  证明: isSuccPrelimit_bot

Depends on / 依赖: isSuccPrelimit_bot
-/
theorem isSuccPrelimit_zero : IsSuccPrelimit (0 : Cardinal) :=
  isSuccPrelimit_bot

/--
theorem `isSuccLimit_iff` / 定理 `isSuccLimit_iff`

English:
theorem isSuccLimit_iff
  given: {c : Cardinal}
  statement: IsSuccLimit c ↔ c != 0 ∧ IsSuccPrelimit c
  proof: isSuccLimit_iff_of_orderBot

@[simp]

中文:
定理 isSuccLimit_iff
  条件: {c : Cardinal}
  结论: IsSuccLimit c ↔ c != 0 ∧ IsSuccPrelimit c
  证明: isSuccLimit_iff_of_orderBot

@[simp]
-/
protected theorem isSuccLimit_iff {c : Cardinal} : IsSuccLimit c ↔ c != 0 ∧ IsSuccPrelimit c :=
  isSuccLimit_iff_of_orderBot

@[simp]
/--
theorem `not_isSuccLimit_zero` / 定理 `not_isSuccLimit_zero`

English:
theorem not_isSuccLimit_zero
  statement: ¬ IsSuccLimit (0 : Cardinal)
  proof: not_isSuccLimit_bot

中文:
定理 not_isSuccLimit_zero
  结论: ¬ IsSuccLimit (0 : Cardinal)
  证明: not_isSuccLimit_bot
-/
protected theorem not_isSuccLimit_zero : ¬ IsSuccLimit (0 : Cardinal) :=
  not_isSuccLimit_bot

/--
Definition of `IsStrongPrelimit` / `IsStrongPrelimit` 的定义

English:
definition IsStrongPrelimit
  signature: (c : Cardinal)
  body: forall ⦃x⦄, x < c -> 2 ^ x < c

中文:
定义 IsStrongPrelimit
  签名: (c : Cardinal)
  定义体: forall ⦃x⦄, x < c -> 2 ^ x < c
-/
def IsStrongPrelimit (c : Cardinal) : Prop :=
  forall ⦃x⦄, x < c -> 2 ^ x < c

/-- A cardinal is a strong limit if it is not zero and it is closed under powersets.
Note that `ℵ₀` is a strong limit by this definition.

See `IsStrongPrelimit` for a version including `0`. -/
@[mk_iff]
/--
Definition of `IsStrongLimit` / `IsStrongLimit` 的定义

English:
structure IsStrongLimit
  parameters: (c : Cardinal)
  axioms and operations (2):
    - ne_zero : c != 0
    - isStrongPrelimit : IsStrongPrelimit c

中文:
结构 IsStrongLimit
  参数: (c : Cardinal)
  公理与运算 (2 个):
    - ne_zero : c != 0
    - isStrongPrelimit : IsStrongPrelimit c
-/
structure IsStrongLimit (c : Cardinal) : Prop where
  ne_zero : c != 0
  protected isStrongPrelimit : IsStrongPrelimit c

@[deprecated (since := "2026-03-31")]
alias IsStrongLimit.two_power_lt := IsStrongLimit.isStrongPrelimit

/--
theorem `IsStrongPrelimit.isSuccPrelimit` / 定理 `IsStrongPrelimit.isSuccPrelimit`

English:
theorem IsStrongPrelimit.isSuccPrelimit
  given: {c} (hc : IsStrongPrelimit c)
  proof: isSuccPrelimit_of_succ_lt fun x hx => (succ_le_of_lt <| cantor x).trans_lt (hc hx)

中文:
定理 IsStrongPrelimit.isSuccPrelimit
  条件: {c} (hc : IsStrongPrelimit c)
  证明: isSuccPrelimit_of_succ_lt fun x hx => (succ_le_of_lt <| cantor x).trans_lt (hc hx)
-/
protected theorem IsStrongPrelimit.isSuccPrelimit {c} (hc : IsStrongPrelimit c) :
    IsSuccPrelimit c :=
  isSuccPrelimit_of_succ_lt fun x hx => (succ_le_of_lt <| cantor x).trans_lt (hc hx)

/--
theorem `IsStrongLimit.isSuccLimit` / 定理 `IsStrongLimit.isSuccLimit`

English:
theorem IsStrongLimit.isSuccLimit
  given: {c} (hc : IsStrongLimit c)
  statement: IsSuccLimit c
  proof: by
  rw [Cardinal.isSuccLimit_iff]
  exact ⟨hc.ne_zero, hc.isStrongPrelimit.isSuccPrelimit⟩

中文:
定理 IsStrongLimit.isSuccLimit
  条件: {c} (hc : IsStrongLimit c)
  结论: IsSuccLimit c
  证明: by
  rw [Cardinal.isSuccLimit_iff]
  exact ⟨hc.ne_zero, hc.isStrongPrelimit.isSuccPrelimit⟩
-/
protected theorem IsStrongLimit.isSuccLimit {c} (hc : IsStrongLimit c) : IsSuccLimit c := by
  rw [Cardinal.isSuccLimit_iff]
  exact ⟨hc.ne_zero, hc.isStrongPrelimit.isSuccPrelimit⟩

/--
theorem `IsStrongLimit.isSuccPrelimit` / 定理 `IsStrongLimit.isSuccPrelimit`

English:
theorem IsStrongLimit.isSuccPrelimit
  given: {c} (H : IsStrongLimit c)
  statement: IsSuccPrelimit c
  proof: H.isSuccLimit.isSuccPrelimit

中文:
定理 IsStrongLimit.isSuccPrelimit
  条件: {c} (H : IsStrongLimit c)
  结论: IsSuccPrelimit c
  证明: H.isSuccLimit.isSuccPrelimit
-/
protected theorem IsStrongLimit.isSuccPrelimit {c} (H : IsStrongLimit c) : IsSuccPrelimit c :=
  H.isSuccLimit.isSuccPrelimit

/--
theorem `not_isStrongPrelimit_iff` / 定理 `not_isStrongPrelimit_iff`

English:
theorem not_isStrongPrelimit_iff
  given: {c}
  statement: ¬ IsStrongPrelimit c ↔ exists x < c, c <= 2 ^ x
  proof: by
  simp [IsStrongPrelimit]

@[simp]

中文:
定理 not_isStrongPrelimit_iff
  条件: {c}
  结论: ¬ IsStrongPrelimit c ↔ 存在 x < c, c <= 2 ^ x
  证明: by
  simp [IsStrongPrelimit]

@[simp]

Depends on / 依赖: IsStrongPrelimit
-/
theorem not_isStrongPrelimit_iff {c} : ¬ IsStrongPrelimit c ↔ exists x < c, c <= 2 ^ x := by
  simp [IsStrongPrelimit]

@[simp]
/--
theorem `IsStrongPrelimit.zero` / 定理 `IsStrongPrelimit.zero`

English:
theorem IsStrongPrelimit.zero
  statement: IsStrongPrelimit 0
  proof: by
  simp [IsStrongPrelimit]

@[simp]

中文:
定理 IsStrongPrelimit.zero
  结论: IsStrongPrelimit 0
  证明: by
  simp [IsStrongPrelimit]

@[simp]

Depends on / 依赖: IsStrongPrelimit
-/
theorem IsStrongPrelimit.zero : IsStrongPrelimit 0 := by
  simp [IsStrongPrelimit]

@[simp]
/--
theorem `not_isStrongLimit_zero` / 定理 `not_isStrongLimit_zero`

English:
theorem not_isStrongLimit_zero
  statement: ¬ IsStrongLimit (0 : Cardinal)
  proof: fun h => h.ne_zero rfl

中文:
定理 not_isStrongLimit_zero
  结论: ¬ IsStrongLimit (0 : Cardinal)
  证明: fun h => h.ne_zero rfl

Depends on / 依赖: h.ne_zero, ne_zero
-/
theorem not_isStrongLimit_zero : ¬ IsStrongLimit (0 : Cardinal) :=
  fun h => h.ne_zero rfl


/--
theorem `lift_le_sum` / 定理 `lift_le_sum`

English:
theorem lift_le_sum
  given: {ι : Type u} (f : ι -> Cardinal.{v}) (i)
  statement: lift.{u, v} (f i) <= sum f
  proof: by
  rw [← Quotient.out_eq (f i)]
  exact ⟨⟨fun a => ⟨i, a.down⟩, fun a b h => by simpa using h⟩⟩

中文:
定理 lift_le_sum
  条件: {ι : 类型u} (f : ι -> Cardinal.{v}) (i)
  结论: lift.{u, v} (f i) <= sum f
  证明: by
  rw [← Quotient.out_eq (f i)]
  exact ⟨⟨fun a => ⟨i, a.down⟩, fun a b h => by simpa using h⟩⟩

Depends on / 依赖: Quotient, Quotient.out_eq, a.down, out_eq
-/
theorem lift_le_sum {ι : Type u} (f : ι -> Cardinal.{v}) (i) : lift.{u, v} (f i) <= sum f := by
  rw [← Quotient.out_eq (f i)]
  exact ⟨⟨fun a => ⟨i, a.down⟩, fun a b h => by simpa using h⟩⟩

/--
theorem `le_sum` / 定理 `le_sum`

English:
theorem le_sum
  given: {ι : Type u} (f : ι -> Cardinal.{max u v}) (i)
  statement: f i <= sum f
  proof: by
  simpa [← lift_umax] using lift_le_sum f i

中文:
定理 le_sum
  条件: {ι : 类型u} (f : ι -> Cardinal.{max u v}) (i)
  结论: f i <= sum f
  证明: by
  simpa [← lift_umax] using lift_le_sum f i

Depends on / 依赖: lift_le_sum, lift_umax
-/
theorem le_sum {ι : Type u} (f : ι -> Cardinal.{max u v}) (i) : f i <= sum f := by
  simpa [← lift_umax] using lift_le_sum f i

/--
theorem `iSup_le_sum` / 定理 `iSup_le_sum`

English:
theorem iSup_le_sum
  given: {ι} (f : ι -> Cardinal)
  statement: iSup f <= sum f
  proof: ciSup_le' le_sum _

中文:
定理 iSup_le_sum
  条件: {ι} (f : ι -> Cardinal)
  结论: iSup f <= sum f
  证明: ciSup_le' le_sum _

Depends on / 依赖: ciSup_le, le_sum
-/
theorem iSup_le_sum {ι} (f : ι -> Cardinal) : iSup f <= sum f :=
ciSup_le' le_sum _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `sum_add_distrib` / 定理 `sum_add_distrib`

English:
theorem sum_add_distrib
  given: {ι} (f g : ι -> Cardinal)
  statement: sum (f + g) = sum f + sum g
  proof: by
  have := mk_congr (Equiv.sigmaSumDistrib (Quotient.out ∘ f) (Quotient.out ∘ g))
  simp only [comp_apply, mk_sigma, mk_sum, mk_out, lift_id] at this
  exact this

@[simp]

中文:
定理 sum_add_distrib
  条件: {ι} (f g : ι -> Cardinal)
  结论: sum (f + g) = sum f + sum g
  证明: by
  have := mk_congr (Equiv.sigmaSumDistrib (Quotient.out ∘ f) (Quotient.out ∘ g))
  simp only [comp_apply, mk_sigma, mk_sum, mk_out, lift_id] at this
  exact this

@[simp]

Depends on / 依赖: Equiv.sigmaSumDistrib, Quotient, Quotient.out, comp_apply, lift_id, mk_congr, mk_out, mk_sigma, mk_sum, sigmaSumDistrib
-/
theorem sum_add_distrib {ι} (f g : ι -> Cardinal) : sum (f + g) = sum f + sum g := by
  have := mk_congr (Equiv.sigmaSumDistrib (Quotient.out ∘ f) (Quotient.out ∘ g))
  simp only [comp_apply, mk_sigma, mk_sum, mk_out, lift_id] at this
  exact this

@[simp]
/--
theorem `sum_add_distrib'` / 定理 `sum_add_distrib'`

English:
theorem sum_add_distrib'
  given: {ι} (f g : ι -> Cardinal)
  proof: sum_add_distrib f g

@[gcongr]

中文:
定理 sum_add_distrib'
  条件: {ι} (f g : ι -> Cardinal)
  证明: sum_add_distrib f g

@[gcongr]

Depends on / 依赖: sum_add_distrib
-/
theorem sum_add_distrib' {ι} (f g : ι -> Cardinal) :
    (Cardinal.sum fun i => f i + g i) = sum f + sum g :=
  sum_add_distrib f g

@[gcongr]
/--
theorem `sum_le_sum` / 定理 `sum_le_sum`

English:
theorem sum_le_sum
  given: {ι} (f g : ι -> Cardinal) (H : forall i, f i <= g i)
  statement: sum f <= sum g
  proof: ⟨(Embedding.refl _).sigmaMap fun i =>
Classical.choice by have := H i; rwa [← Quot.out_eq (f i), ← Quot.out_eq (g i)] at this⟩

中文:
定理 sum_le_sum
  条件: {ι} (f g : ι -> Cardinal) (H : 对任意 i, f i <= g i)
  结论: sum f <= sum g
  证明: ⟨(Embedding.refl _).sigmaMap fun i =>
Classical.choice by have := H i; rwa [← Quot.out_eq (f i), ← Quot.out_eq (g i)] at this⟩

Depends on / 依赖: Classical, Classical.choice, Embedding, Embedding.refl, Quot.out_eq, choice, out_eq, sigmaMap
-/
theorem sum_le_sum {ι} (f g : ι -> Cardinal) (H : forall i, f i <= g i) : sum f <= sum g :=
  ⟨(Embedding.refl _).sigmaMap fun i =>
Classical.choice by have := H i; rwa [← Quot.out_eq (f i), ← Quot.out_eq (g i)] at this⟩

/--
theorem `mk_le_mk_mul_of_mk_preimage_le` / 定理 `mk_le_mk_mul_of_mk_preimage_le`

English:
theorem mk_le_mk_mul_of_mk_preimage_le
  given: {c : Cardinal} (f : α -> β) (hf : forall b : β, #(f ⁻¹' {b}) <= c)
  proof: by
  simpa only [← mk_congr (@Equiv.sigmaFiberEquiv α β f), mk_sigma, ← sum_const'] using!
    sum_le_sum _ _ hf

中文:
定理 mk_le_mk_mul_of_mk_preimage_le
  条件: {c : Cardinal} (f : α -> β) (hf : 对任意 b : β, #(f ⁻¹' {b}) <= c)
  证明: by
  simpa only [← mk_congr (@Equiv.sigmaFiberEquiv α β f), mk_sigma, ← sum_const'] using!
    sum_le_sum _ _ hf

Depends on / 依赖: Equiv.sigmaFiberEquiv, mk_congr, mk_sigma, sigmaFiberEquiv, sum_const, sum_le_sum
-/
theorem mk_le_mk_mul_of_mk_preimage_le {c : Cardinal} (f : α -> β) (hf : forall b : β, #(f ⁻¹' {b}) <= c) :
    #α <= #β * c := by
  simpa only [← mk_congr (@Equiv.sigmaFiberEquiv α β f), mk_sigma, ← sum_const'] using!
    sum_le_sum _ _ hf

/--
theorem `lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le` / 定理 `lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le`

English:
theorem lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le
  statement: {α : Type u} {β : Type v} {c : Cardinal}
  proof: (mk_le_mk_mul_of_mk_preimage_le fun x : ULift.{v} α => ULift.up.{u} (f x.1))
    ULift.forall.2 fun b =>
      (mk_congr <|
            (Equiv.ulift.image _).trans
              (Equiv.trans
                (by
                  rw [Equiv.image_eq_preimage_symm]
                  simp only [preimage

中文:
定理 lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le
  结论: {α : 类型u} {β : 类型v} {c : Cardinal}
  证明: (mk_le_mk_mul_of_mk_preimage_le fun x : ULift.{v} α => ULift.up.{u} (f x.1))
    ULift.forall.2 fun b =>
      (mk_congr <|
            (Equiv.ulift.image _).trans
              (Equiv.trans
                (by
                  rw [Equiv.image_eq_preimage_symm]
                  simp only [preimage

Depends on / 依赖: Equiv.image_eq_preimage_symm, Equiv.refl, Equiv.trans, Equiv.ulift.image, Equiv.ulift.symm, ULift.forall, ULift.up, ULift.up_inj, coe_ofPred, image_eq_preimage_symm, mem_ofPred_eq, mem_singleton_iff, mk_congr, mk_le_mk_mul_of_mk_preimage_le, preimage, trans_le, up_inj
-/
theorem lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le {α : Type u} {β : Type v} {c : Cardinal}
    (f : α -> β) (hf : forall b : β, lift.{v} #(f ⁻¹' {b}) <= c) : lift.{v} #α <= lift.{u} #β * c :=
(mk_le_mk_mul_of_mk_preimage_le fun x : ULift.{v} α => ULift.up.{u} (f x.1))
    ULift.forall.2 fun b =>
      (mk_congr <|
            (Equiv.ulift.image _).trans
              (Equiv.trans
                (by
                  rw [Equiv.image_eq_preimage_symm]
                  simp only [preimage, mem_singleton_iff, ULift.up_inj, mem_ofPred_eq, coe_ofPred]
                  exact Equiv.refl _)
                Equiv.ulift.symm)).trans_le
        (hf b)

end Cardinal

/-! ### Well-ordering theorem -/

open Cardinal in
/--
theorem `nonempty_embedding_to_cardinal` / 定理 `nonempty_embedding_to_cardinal`

English:
theorem nonempty_embedding_to_cardinal
  statement: Nonempty (α ↪ Cardinal.{u})
  proof: (Embedding.total _ _).resolve_left fun ⟨⟨f, hf⟩⟩ =>
    let g : α -> Cardinal.{u} := invFun f
    let ⟨x, (hx : g x = 2 ^ sum g)⟩ := invFun_surjective hf (2 ^ sum g)
    have : g x <= sum g := le_sum.{u, u} g x
    not_le_of_gt (by rw [hx]; exact cantor _) this

中文:
定理 nonempty_embedding_to_cardinal
  结论: Nonempty (α ↪ Cardinal.{u})
  证明: (Embedding.total _ _).resolve_left fun ⟨⟨f, hf⟩⟩ =>
    let g : α -> Cardinal.{u} := invFun f
    let ⟨x, (hx : g x = 2 ^ sum g)⟩ := invFun_surjective hf (2 ^ sum g)
    have : g x <= sum g := le_sum.{u, u} g x
    not_le_of_gt (by rw [hx]; exact cantor _) this

Depends on / 依赖: Cardinal, Embedding, Embedding.total, cantor, invFun, invFun_surjective, le_sum, not_le_of_gt, resolve_left
-/
theorem nonempty_embedding_to_cardinal : Nonempty (α ↪ Cardinal.{u}) :=
  (Embedding.total _ _).resolve_left fun ⟨⟨f, hf⟩⟩ =>
    let g : α -> Cardinal.{u} := invFun f
    let ⟨x, (hx : g x = 2 ^ sum g)⟩ := invFun_surjective hf (2 ^ sum g)
    have : g x <= sum g := le_sum.{u, u} g x
    not_le_of_gt (by rw [hx]; exact cantor _) this

/--
Definition of `embeddingToCardinal` / `embeddingToCardinal` 的定义

English:
definition embeddingToCardinal
  signature: : α ↪ Cardinal.{u}
  body: Classical.choice nonempty_embedding_to_cardinal

中文:
定义 embeddingToCardinal
  签名: : α ↪ Cardinal.{u}
  定义体: Classical.choice nonempty_embedding_to_cardinal

Depends on / 依赖: Classical, Classical.choice, choice, nonempty_embedding_to_cardinal
-/
def embeddingToCardinal : α ↪ Cardinal.{u} :=
  Classical.choice nonempty_embedding_to_cardinal

/--
Definition of `WellOrderingRel` / `WellOrderingRel` 的定义

English:
definition WellOrderingRel
  signature: : α -> α -> Prop
  body: embeddingToCardinal ⁻¹'o (· < ·)

中文:
定义 WellOrderingRel
  签名: : α -> α -> 命题
  定义体: embeddingToCardinal ⁻¹'o (· < ·)

Depends on / 依赖: embeddingToCardinal
-/
def WellOrderingRel : α -> α -> Prop :=
  embeddingToCardinal ⁻¹'o (· < ·)

/--
Instance `WellOrderingRel.isWellOrder` / 实例 `WellOrderingRel.isWellOrder`

English:
instance WellOrderingRel.isWellOrder
  signature: : IsWellOrder α WellOrderingRel
  body: (RelEmbedding.preimage _ _).isWellOrder

中文:
实例 WellOrderingRel.isWellOrder
  签名: : IsWellOrder α WellOrderingRel
  定义体: (RelEmbedding.preimage _ _).isWellOrder

Depends on / 依赖: RelEmbedding, RelEmbedding.preimage, isWellOrder, preimage
-/
instance WellOrderingRel.isWellOrder : IsWellOrder α WellOrderingRel :=
  (RelEmbedding.preimage _ _).isWellOrder

/--
Instance `IsWellOrder.subtype_nonempty` / 实例 `IsWellOrder.subtype_nonempty`

English:
instance IsWellOrder.subtype_nonempty
  signature: : Nonempty { r // IsWellOrder α r }
  body: ⟨⟨WellOrderingRel, inferInstance⟩⟩

中文:
实例 IsWellOrder.subtype_nonempty
  签名: : Nonempty { r // IsWellOrder α r }
  定义体: ⟨⟨WellOrderingRel, inferInstance⟩⟩

Depends on / 依赖: WellOrderingRel
-/
instance IsWellOrder.subtype_nonempty : Nonempty { r // IsWellOrder α r } :=
  ⟨⟨WellOrderingRel, inferInstance⟩⟩

variable (α) in
/--
theorem `exists_wellFoundedLT` / 定理 `exists_wellFoundedLT`

English:
theorem exists_wellFoundedLT
  statement: exists (_ : LinearOrder α), WellFoundedLT α
  proof: by
  classical
  exact ⟨linearOrderOfSTO WellOrderingRel, ⟨WellOrderingRel.isWellOrder.wf⟩⟩

中文:
定理 exists_wellFoundedLT
  结论: 存在 (_ : LinearOrder α), WellFoundedLT α
  证明: by
  classical
  exact ⟨linearOrderOfSTO WellOrderingRel, ⟨WellOrderingRel.isWellOrder.wf⟩⟩

Depends on / 依赖: WellOrderingRel, WellOrderingRel.isWellOrder.wf, classical, isWellOrder, linearOrderOfSTO
-/
theorem exists_wellFoundedLT : exists (_ : LinearOrder α), WellFoundedLT α := by
  classical
  exact ⟨linearOrderOfSTO WellOrderingRel, ⟨WellOrderingRel.isWellOrder.wf⟩⟩

variable (α) in
/-- The **well-ordering theorem** (or **Zermelo's theorem**): every type can be co-well-ordered. -/
@[to_dual existing]
/--
lemma `exists_wellFoundedGT` / 引理 `exists_wellFoundedGT`

English:
lemma exists_wellFoundedGT
  statement: exists (_ : LinearOrder α), WellFoundedGT α
  proof: by
  classical
  exact ⟨linearOrderOfSTO (Function.swap WellOrderingRel), ⟨WellOrderingRel.isWellOrder.wf⟩⟩

@[deprecated (since := "2026-04-12")] alias exists_wellOrder := exists_wellFoundedLT

中文:
引理 exists_wellFoundedGT
  结论: 存在 (_ : LinearOrder α), WellFoundedGT α
  证明: by
  classical
  exact ⟨linearOrderOfSTO (Function.swap WellOrderingRel), ⟨WellOrderingRel.isWellOrder.wf⟩⟩

@[deprecated (since := "2026-04-12")] alias exists_wellOrder := exists_wellFoundedLT

Depends on / 依赖: Function, Function.swap, WellOrderingRel, WellOrderingRel.isWellOrder.wf, classical, isWellOrder, linearOrderOfSTO
-/
lemma exists_wellFoundedGT : exists (_ : LinearOrder α), WellFoundedGT α := by
  classical
  exact ⟨linearOrderOfSTO (Function.swap WellOrderingRel), ⟨WellOrderingRel.isWellOrder.wf⟩⟩

@[deprecated (since := "2026-04-12")] alias exists_wellOrder := exists_wellFoundedLT

namespace Cardinal

@[deprecated exists_eq_ciSup_of_not_isSuccPrelimit (since := "2026-04-13")]
/--
lemma `exists_eq_of_iSup_eq_of_not_isSuccPrelimit` / 引理 `exists_eq_of_iSup_eq_of_not_isSuccPrelimit`

English:
lemma exists_eq_of_iSup_eq_of_not_isSuccPrelimit
  proof: by
  subst h
  exact exists_eq_ciSup_of_not_isSuccPrelimit hω

@[deprecated exists_eq_ciSup_of_not_isSuccLimit (since := "2026-04-13")]

中文:
引理 exists_eq_of_iSup_eq_of_not_isSuccPrelimit
  证明: by
  subst h
  exact exists_eq_ciSup_of_not_isSuccPrelimit hω

@[deprecated exists_eq_ciSup_of_not_isSuccLimit (since := "2026-04-13")]

Depends on / 依赖: exists_eq_ciSup_of_not_isSuccPrelimit
-/
lemma exists_eq_of_iSup_eq_of_not_isSuccPrelimit
    {ι : Type u} (f : ι -> Cardinal.{v}) (ω : Cardinal.{v})
    (hω : ¬ IsSuccPrelimit ω)
    (h : ⨆ i : ι, f i = ω) : exists i, f i = ω := by
  subst h
  exact exists_eq_ciSup_of_not_isSuccPrelimit hω

@[deprecated exists_eq_ciSup_of_not_isSuccLimit (since := "2026-04-13")]
/--
lemma `exists_eq_of_iSup_eq_of_not_isSuccLimit` / 引理 `exists_eq_of_iSup_eq_of_not_isSuccLimit`

English:
lemma exists_eq_of_iSup_eq_of_not_isSuccLimit
  proof: by
  subst h
  exact exists_eq_ciSup_of_not_isSuccLimit hf hc

中文:
引理 exists_eq_of_iSup_eq_of_not_isSuccLimit
  证明: by
  subst h
  exact exists_eq_ciSup_of_not_isSuccLimit hf hc

Depends on / 依赖: exists_eq_ciSup_of_not_isSuccLimit
-/
lemma exists_eq_of_iSup_eq_of_not_isSuccLimit
    {ι : Type u} [hι : Nonempty ι] (f : ι -> Cardinal.{v}) (hf : BddAbove (range f))
    {c : Cardinal.{v}} (hc : ¬ IsSuccLimit c)
    (h : ⨆ i, f i = c) : exists i, f i = c := by
  subst h
  exact exists_eq_ciSup_of_not_isSuccLimit hf hc

/-! ### Indexed cardinal `prod` -/

/--
theorem `sum_lt_prod` / 定理 `sum_lt_prod`

English:
theorem sum_lt_prod
  given: {ι} (f g : ι -> Cardinal) (H : forall i, f i < g i)
  statement: sum f < prod g
  proof: lt_of_not_ge fun ⟨F⟩ => by
    have : Inhabited (forall i : ι, (g i).out) := by
refine ⟨fun i => Classical.choice mk_ne_zero_iff.1 ?_⟩
      rw [mk_out]
      exact (H i).ne_bot
    let G := invFun F
    have sG : Surjective G := invFun_surjective F.2
    choose C hc using
      show forall i, exist

中文:
定理 sum_lt_prod
  条件: {ι} (f g : ι -> Cardinal) (H : 对任意 i, f i < g i)
  结论: sum f < prod g
  证明: lt_of_not_ge fun ⟨F⟩ => by
    have : Inhabited (forall i : ι, (g i).out) := by
refine ⟨fun i => Classical.choice mk_ne_zero_iff.1 ?_⟩
      rw [mk_out]
      exact (H i).ne_bot
    let G := invFun F
    have sG : Surjective G := invFun_surjective F.2
    choose C hc using
      show forall i, exist

Depends on / 依赖: Classical, Classical.choice, Embedding, Embedding.ofSurjective, Inhabited, Surjective, choice, invFun, invFun_surjective, lt_of_not_ge, mk_ne_zero_iff, mk_out, ne_bot, not_exists, not_exists.symm, not_forall, not_forall.symm, not_ge, ofSurjective
-/
theorem sum_lt_prod {ι} (f g : ι -> Cardinal) (H : forall i, f i < g i) : sum f < prod g :=
  lt_of_not_ge fun ⟨F⟩ => by
    have : Inhabited (forall i : ι, (g i).out) := by
refine ⟨fun i => Classical.choice mk_ne_zero_iff.1 ?_⟩
      rw [mk_out]
      exact (H i).ne_bot
    let G := invFun F
    have sG : Surjective G := invFun_surjective F.2
    choose C hc using
      show forall i, exists b, forall a, G ⟨i, a⟩ i != b by
        intro i
        simp only [not_exists.symm, not_forall.symm]
        refine fun h => (H i).not_ge ?_
        rw [← mk_out (f i)]; rw [← mk_out (g i)]
        exact ⟨Embedding.ofSurjective _ h⟩
    let ⟨⟨i, a⟩, h⟩ := sG C
    exact hc i a (congr_fun h _)

/--
theorem `prod_le_prod` / 定理 `prod_le_prod`

English:
theorem prod_le_prod
  given: {ι} (f g : ι -> Cardinal) (H : forall i, f i <= g i)
  statement: prod f <= prod g
  proof: ⟨Embedding.piCongrRight fun i =>
Classical.choice by have := H i; rwa [← mk_out (f i), ← mk_out (g i)] at this⟩

中文:
定理 prod_le_prod
  条件: {ι} (f g : ι -> Cardinal) (H : 对任意 i, f i <= g i)
  结论: prod f <= prod g
  证明: ⟨Embedding.piCongrRight fun i =>
Classical.choice by have := H i; rwa [← mk_out (f i), ← mk_out (g i)] at this⟩

Depends on / 依赖: Classical, Classical.choice, Embedding, Embedding.piCongrRight, choice, mk_out, piCongrRight
-/
theorem prod_le_prod {ι} (f g : ι -> Cardinal) (H : forall i, f i <= g i) : prod f <= prod g :=
  ⟨Embedding.piCongrRight fun i =>
Classical.choice by have := H i; rwa [← mk_out (f i), ← mk_out (g i)] at this⟩


/--
theorem `aleph0_pos` / 定理 `aleph0_pos`

English:
theorem aleph0_pos
  statement: 0 < ℵ₀
  proof: pos_iff_ne_zero.2 aleph0_ne_zero

@[simp]

中文:
定理 aleph0_pos
  结论: 0 < ℵ₀
  证明: pos_iff_ne_zero.2 aleph0_ne_zero

@[simp]

Depends on / 依赖: aleph0_ne_zero, pos_iff_ne_zero
-/
theorem aleph0_pos : 0 < ℵ₀ :=
  pos_iff_ne_zero.2 aleph0_ne_zero

@[simp]
/--
theorem `aleph0_le_lift` / 定理 `aleph0_le_lift`

English:
theorem aleph0_le_lift
  given: {c : Cardinal.{u}}
  statement: ℵ₀ <= lift.{v} c ↔ ℵ₀ <= c
  proof: by
  simpa using lift_le (a := ℵ₀)

@[simp]

中文:
定理 aleph0_le_lift
  条件: {c : Cardinal.{u}}
  结论: ℵ₀ <= lift.{v} c ↔ ℵ₀ <= c
  证明: by
  simpa using lift_le (a := ℵ₀)

@[simp]

Depends on / 依赖: lift_le
-/
theorem aleph0_le_lift {c : Cardinal.{u}} : ℵ₀ <= lift.{v} c ↔ ℵ₀ <= c := by
  simpa using lift_le (a := ℵ₀)

@[simp]
/--
theorem `lift_le_aleph0` / 定理 `lift_le_aleph0`

English:
theorem lift_le_aleph0
  given: {c : Cardinal.{u}}
  statement: lift.{v} c <= ℵ₀ ↔ c <= ℵ₀
  proof: by
  simpa using lift_le (b := ℵ₀)

@[simp]

中文:
定理 lift_le_aleph0
  条件: {c : Cardinal.{u}}
  结论: lift.{v} c <= ℵ₀ ↔ c <= ℵ₀
  证明: by
  simpa using lift_le (b := ℵ₀)

@[simp]

Depends on / 依赖: lift_le
-/
theorem lift_le_aleph0 {c : Cardinal.{u}} : lift.{v} c <= ℵ₀ ↔ c <= ℵ₀ := by
  simpa using lift_le (b := ℵ₀)

@[simp]
/--
theorem `aleph0_lt_lift` / 定理 `aleph0_lt_lift`

English:
theorem aleph0_lt_lift
  given: {c : Cardinal.{u}}
  statement: ℵ₀ < lift.{v} c ↔ ℵ₀ < c
  proof: by
  simpa using lift_lt (a := ℵ₀)

@[simp]

中文:
定理 aleph0_lt_lift
  条件: {c : Cardinal.{u}}
  结论: ℵ₀ < lift.{v} c ↔ ℵ₀ < c
  证明: by
  simpa using lift_lt (a := ℵ₀)

@[simp]

Depends on / 依赖: lift_lt
-/
theorem aleph0_lt_lift {c : Cardinal.{u}} : ℵ₀ < lift.{v} c ↔ ℵ₀ < c := by
  simpa using lift_lt (a := ℵ₀)

@[simp]
/--
theorem `lift_lt_aleph0` / 定理 `lift_lt_aleph0`

English:
theorem lift_lt_aleph0
  given: {c : Cardinal.{u}}
  statement: lift.{v} c < ℵ₀ ↔ c < ℵ₀
  proof: by
  simpa using lift_lt (b := ℵ₀)

@[simp]

中文:
定理 lift_lt_aleph0
  条件: {c : Cardinal.{u}}
  结论: lift.{v} c < ℵ₀ ↔ c < ℵ₀
  证明: by
  simpa using lift_lt (b := ℵ₀)

@[simp]

Depends on / 依赖: lift_lt
-/
theorem lift_lt_aleph0 {c : Cardinal.{u}} : lift.{v} c < ℵ₀ ↔ c < ℵ₀ := by
  simpa using lift_lt (b := ℵ₀)

@[simp]
/--
theorem `aleph0_eq_lift` / 定理 `aleph0_eq_lift`

English:
theorem aleph0_eq_lift
  given: {c : Cardinal.{u}}
  statement: ℵ₀ = lift.{v} c ↔ ℵ₀ = c
  proof: by
  simpa using lift_inj (a := ℵ₀)

@[simp]

中文:
定理 aleph0_eq_lift
  条件: {c : Cardinal.{u}}
  结论: ℵ₀ = lift.{v} c ↔ ℵ₀ = c
  证明: by
  simpa using lift_inj (a := ℵ₀)

@[simp]

Depends on / 依赖: lift_inj
-/
theorem aleph0_eq_lift {c : Cardinal.{u}} : ℵ₀ = lift.{v} c ↔ ℵ₀ = c := by
  simpa using lift_inj (a := ℵ₀)

@[simp]
/--
theorem `lift_eq_aleph0` / 定理 `lift_eq_aleph0`

English:
theorem lift_eq_aleph0
  given: {c : Cardinal.{u}}
  statement: lift.{v} c = ℵ₀ ↔ c = ℵ₀
  proof: by
  simp [eqComm]

中文:
定理 lift_eq_aleph0
  条件: {c : Cardinal.{u}}
  结论: lift.{v} c = ℵ₀ ↔ c = ℵ₀
  证明: by
  simp [eqComm]

Depends on / 依赖: eqComm
-/
theorem lift_eq_aleph0 {c : Cardinal.{u}} : lift.{v} c = ℵ₀ ↔ c = ℵ₀ := by
  simp [eqComm]


/--
theorem `mk_fin` / 定理 `mk_fin`

English:
theorem mk_fin
  given: (n : Nat)
  statement: #(Fin n) = n
  proof: by simp

@[simp]

中文:
定理 mk_fin
  条件: (n : 自然数)
  结论: #(Fin n) = n
  证明: by simp

@[simp]
-/
theorem mk_fin (n : Nat) : #(Fin n) = n := by simp

@[simp]
/--
theorem `lift_natCast` / 定理 `lift_natCast`

English:
theorem lift_natCast
  given: (n : Nat)
  statement: lift.{u} (n : Cardinal.{v}) = n
  proof: by induction n <;> simp [*]

@[simp]

中文:
定理 lift_natCast
  条件: (n : 自然数)
  结论: lift.{u} (n : Cardinal.{v}) = n
  证明: by induction n <;> simp [*]

@[simp]
-/
theorem lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{v}) = n := by induction n <;> simp [*]

@[simp]
/--
theorem `lift_ofNat` / 定理 `lift_ofNat`

English:
theorem lift_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: lift_natCast n

@[simp]

中文:
定理 lift_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: lift_natCast n

@[simp]

Depends on / 依赖: lift_natCast
-/
theorem lift_ofNat (n : Nat) [n.AtLeastTwo] :
    lift.{u} (ofNat(n) : Cardinal.{v}) = OfNat.ofNat n :=
  lift_natCast n

@[simp]
/--
theorem `lift_eq_nat_iff` / 定理 `lift_eq_nat_iff`

English:
theorem lift_eq_nat_iff
  given: {a : Cardinal.{u}} {n : Nat}
  statement: lift.{v} a = n ↔ a = n
  proof: lift_injective.eq_iff' (lift_natCast n)

@[simp]

中文:
定理 lift_eq_nat_iff
  条件: {a : Cardinal.{u}} {n : 自然数}
  结论: lift.{v} a = n ↔ a = n
  证明: lift_injective.eq_iff' (lift_natCast n)

@[simp]

Depends on / 依赖: eq_iff, lift_injective, lift_injective.eq_iff, lift_natCast
-/
theorem lift_eq_nat_iff {a : Cardinal.{u}} {n : Nat} : lift.{v} a = n ↔ a = n :=
  lift_injective.eq_iff' (lift_natCast n)

@[simp]
/--
theorem `lift_eq_ofNat_iff` / 定理 `lift_eq_ofNat_iff`

English:
theorem lift_eq_ofNat_iff
  given: {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo]
  proof: lift_eq_nat_iff

@[simp]

中文:
定理 lift_eq_ofNat_iff
  条件: {a : Cardinal.{u}} {n : 自然数} [n.AtLeastTwo]
  证明: lift_eq_nat_iff

@[simp]

Depends on / 依赖: lift_eq_nat_iff
-/
theorem lift_eq_ofNat_iff {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo] :
    lift.{v} a = ofNat(n) ↔ a = OfNat.ofNat n :=
  lift_eq_nat_iff

@[simp]
/--
theorem `nat_eq_lift_iff` / 定理 `nat_eq_lift_iff`

English:
theorem nat_eq_lift_iff
  given: {n : Nat} {a : Cardinal.{u}}
  proof: by
  rw [← lift_natCast.{v]; rw [u} n]; rw [lift_inj]

@[simp]

中文:
定理 nat_eq_lift_iff
  条件: {n : 自然数} {a : Cardinal.{u}}
  证明: by
  rw [← lift_natCast.{v]; rw [u} n]; rw [lift_inj]

@[simp]

Depends on / 依赖: lift_inj, lift_natCast
-/
theorem nat_eq_lift_iff {n : Nat} {a : Cardinal.{u}} :
    (n : Cardinal) = lift.{v} a ↔ (n : Cardinal) = a := by
  rw [← lift_natCast.{v]; rw [u} n]; rw [lift_inj]

@[simp]
/--
theorem `zero_eq_lift_iff` / 定理 `zero_eq_lift_iff`

English:
theorem zero_eq_lift_iff
  given: {a : Cardinal.{u}}
  proof: by
  simp [eqComm]

@[simp]

中文:
定理 zero_eq_lift_iff
  条件: {a : Cardinal.{u}}
  证明: by
  simp [eqComm]

@[simp]

Depends on / 依赖: eqComm
-/
theorem zero_eq_lift_iff {a : Cardinal.{u}} :
    (0 : Cardinal) = lift.{v} a ↔ 0 = a := by
  simp [eqComm]

@[simp]
/--
theorem `one_eq_lift_iff` / 定理 `one_eq_lift_iff`

English:
theorem one_eq_lift_iff
  given: {a : Cardinal.{u}}
  proof: by
  simp [eqComm]

@[simp]

中文:
定理 one_eq_lift_iff
  条件: {a : Cardinal.{u}}
  证明: by
  simp [eqComm]

@[simp]

Depends on / 依赖: eqComm
-/
theorem one_eq_lift_iff {a : Cardinal.{u}} :
    (1 : Cardinal) = lift.{v} a ↔ 1 = a := by
  simp [eqComm]

@[simp]
/--
theorem `ofNat_eq_lift_iff` / 定理 `ofNat_eq_lift_iff`

English:
theorem ofNat_eq_lift_iff
  given: {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo]
  proof: nat_eq_lift_iff

@[simp]

中文:
定理 ofNat_eq_lift_iff
  条件: {a : Cardinal.{u}} {n : 自然数} [n.AtLeastTwo]
  证明: nat_eq_lift_iff

@[simp]

Depends on / 依赖: nat_eq_lift_iff
-/
theorem ofNat_eq_lift_iff {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) = lift.{v} a ↔ (OfNat.ofNat n : Cardinal) = a :=
  nat_eq_lift_iff

@[simp]
/--
theorem `lift_le_nat_iff` / 定理 `lift_le_nat_iff`

English:
theorem lift_le_nat_iff
  given: {a : Cardinal.{u}} {n : Nat}
  statement: lift.{v} a <= n ↔ a <= n
  proof: by
  rw [← lift_natCast.{v]; rw [u}]; rw [lift_le]

@[simp]

中文:
定理 lift_le_nat_iff
  条件: {a : Cardinal.{u}} {n : 自然数}
  结论: lift.{v} a <= n ↔ a <= n
  证明: by
  rw [← lift_natCast.{v]; rw [u}]; rw [lift_le]

@[simp]

Depends on / 依赖: lift_le, lift_natCast
-/
theorem lift_le_nat_iff {a : Cardinal.{u}} {n : Nat} : lift.{v} a <= n ↔ a <= n := by
  rw [← lift_natCast.{v]; rw [u}]; rw [lift_le]

@[simp]
/--
theorem `lift_le_one_iff` / 定理 `lift_le_one_iff`

English:
theorem lift_le_one_iff
  given: {a : Cardinal.{u}}
  proof: by
  simpa using lift_le_nat_iff (n := 1)

@[simp]

中文:
定理 lift_le_one_iff
  条件: {a : Cardinal.{u}}
  证明: by
  simpa using lift_le_nat_iff (n := 1)

@[simp]

Depends on / 依赖: lift_le_nat_iff
-/
theorem lift_le_one_iff {a : Cardinal.{u}} :
    lift.{v} a <= 1 ↔ a <= 1 := by
  simpa using lift_le_nat_iff (n := 1)

@[simp]
/--
theorem `lift_le_ofNat_iff` / 定理 `lift_le_ofNat_iff`

English:
theorem lift_le_ofNat_iff
  given: {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo]
  proof: lift_le_nat_iff

@[simp]

中文:
定理 lift_le_ofNat_iff
  条件: {a : Cardinal.{u}} {n : 自然数} [n.AtLeastTwo]
  证明: lift_le_nat_iff

@[simp]

Depends on / 依赖: lift_le_nat_iff
-/
theorem lift_le_ofNat_iff {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo] :
    lift.{v} a <= ofNat(n) ↔ a <= OfNat.ofNat n :=
  lift_le_nat_iff

@[simp]
/--
theorem `nat_le_lift_iff` / 定理 `nat_le_lift_iff`

English:
theorem nat_le_lift_iff
  given: {n : Nat} {a : Cardinal.{u}}
  statement: n <= lift.{v} a ↔ n <= a
  proof: by
  rw [← lift_natCast.{v]; rw [u}]; rw [lift_le]

@[simp]

中文:
定理 nat_le_lift_iff
  条件: {n : 自然数} {a : Cardinal.{u}}
  结论: n <= lift.{v} a ↔ n <= a
  证明: by
  rw [← lift_natCast.{v]; rw [u}]; rw [lift_le]

@[simp]

Depends on / 依赖: lift_le, lift_natCast
-/
theorem nat_le_lift_iff {n : Nat} {a : Cardinal.{u}} : n <= lift.{v} a ↔ n <= a := by
  rw [← lift_natCast.{v]; rw [u}]; rw [lift_le]

@[simp]
/--
theorem `one_le_lift_iff` / 定理 `one_le_lift_iff`

English:
theorem one_le_lift_iff
  given: {a : Cardinal.{u}}
  proof: by
  simpa using nat_le_lift_iff (n := 1)

@[simp]

中文:
定理 one_le_lift_iff
  条件: {a : Cardinal.{u}}
  证明: by
  simpa using nat_le_lift_iff (n := 1)

@[simp]

Depends on / 依赖: nat_le_lift_iff
-/
theorem one_le_lift_iff {a : Cardinal.{u}} :
    (1 : Cardinal) <= lift.{v} a ↔ 1 <= a := by
  simpa using nat_le_lift_iff (n := 1)

@[simp]
/--
theorem `ofNat_le_lift_iff` / 定理 `ofNat_le_lift_iff`

English:
theorem ofNat_le_lift_iff
  given: {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo]
  proof: nat_le_lift_iff

@[simp]

中文:
定理 ofNat_le_lift_iff
  条件: {a : Cardinal.{u}} {n : 自然数} [n.AtLeastTwo]
  证明: nat_le_lift_iff

@[simp]

Depends on / 依赖: nat_le_lift_iff
-/
theorem ofNat_le_lift_iff {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) <= lift.{v} a ↔ (OfNat.ofNat n : Cardinal) <= a :=
  nat_le_lift_iff

@[simp]
/--
theorem `lift_lt_nat_iff` / 定理 `lift_lt_nat_iff`

English:
theorem lift_lt_nat_iff
  given: {a : Cardinal.{u}} {n : Nat}
  statement: lift.{v} a < n ↔ a < n
  proof: by
  rw [← lift_natCast.{v]; rw [u}]; rw [lift_lt]

@[simp]

中文:
定理 lift_lt_nat_iff
  条件: {a : Cardinal.{u}} {n : 自然数}
  结论: lift.{v} a < n ↔ a < n
  证明: by
  rw [← lift_natCast.{v]; rw [u}]; rw [lift_lt]

@[simp]

Depends on / 依赖: lift_lt, lift_natCast
-/
theorem lift_lt_nat_iff {a : Cardinal.{u}} {n : Nat} : lift.{v} a < n ↔ a < n := by
  rw [← lift_natCast.{v]; rw [u}]; rw [lift_lt]

@[simp]
/--
theorem `lift_lt_ofNat_iff` / 定理 `lift_lt_ofNat_iff`

English:
theorem lift_lt_ofNat_iff
  given: {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo]
  proof: lift_lt_nat_iff

@[simp]

中文:
定理 lift_lt_ofNat_iff
  条件: {a : Cardinal.{u}} {n : 自然数} [n.AtLeastTwo]
  证明: lift_lt_nat_iff

@[simp]

Depends on / 依赖: lift_lt_nat_iff
-/
theorem lift_lt_ofNat_iff {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo] :
    lift.{v} a < ofNat(n) ↔ a < OfNat.ofNat n :=
  lift_lt_nat_iff

@[simp]
/--
theorem `nat_lt_lift_iff` / 定理 `nat_lt_lift_iff`

English:
theorem nat_lt_lift_iff
  given: {n : Nat} {a : Cardinal.{u}}
  statement: n < lift.{v} a ↔ n < a
  proof: by
  rw [← lift_natCast.{v]; rw [u}]; rw [lift_lt]

@[simp]

中文:
定理 nat_lt_lift_iff
  条件: {n : 自然数} {a : Cardinal.{u}}
  结论: n < lift.{v} a ↔ n < a
  证明: by
  rw [← lift_natCast.{v]; rw [u}]; rw [lift_lt]

@[simp]

Depends on / 依赖: lift_lt, lift_natCast
-/
theorem nat_lt_lift_iff {n : Nat} {a : Cardinal.{u}} : n < lift.{v} a ↔ n < a := by
  rw [← lift_natCast.{v]; rw [u}]; rw [lift_lt]

@[simp]
/--
theorem `zero_lt_lift_iff` / 定理 `zero_lt_lift_iff`

English:
theorem zero_lt_lift_iff
  given: {a : Cardinal.{u}}
  proof: by
  simpa using nat_lt_lift_iff (n := 0)

@[simp]

中文:
定理 zero_lt_lift_iff
  条件: {a : Cardinal.{u}}
  证明: by
  simpa using nat_lt_lift_iff (n := 0)

@[simp]

Depends on / 依赖: nat_lt_lift_iff
-/
theorem zero_lt_lift_iff {a : Cardinal.{u}} :
    (0 : Cardinal) < lift.{v} a ↔ 0 < a := by
  simpa using nat_lt_lift_iff (n := 0)

@[simp]
/--
theorem `one_lt_lift_iff` / 定理 `one_lt_lift_iff`

English:
theorem one_lt_lift_iff
  given: {a : Cardinal.{u}}
  proof: by
  simpa using nat_lt_lift_iff (n := 1)

@[simp]

中文:
定理 one_lt_lift_iff
  条件: {a : Cardinal.{u}}
  证明: by
  simpa using nat_lt_lift_iff (n := 1)

@[simp]

Depends on / 依赖: nat_lt_lift_iff
-/
theorem one_lt_lift_iff {a : Cardinal.{u}} :
    (1 : Cardinal) < lift.{v} a ↔ 1 < a := by
  simpa using nat_lt_lift_iff (n := 1)

@[simp]
/--
theorem `ofNat_lt_lift_iff` / 定理 `ofNat_lt_lift_iff`

English:
theorem ofNat_lt_lift_iff
  given: {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo]
  proof: nat_lt_lift_iff

中文:
定理 ofNat_lt_lift_iff
  条件: {a : Cardinal.{u}} {n : 自然数} [n.AtLeastTwo]
  证明: nat_lt_lift_iff

Depends on / 依赖: nat_lt_lift_iff
-/
theorem ofNat_lt_lift_iff {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) < lift.{v} a ↔ (OfNat.ofNat n : Cardinal) < a :=
  nat_lt_lift_iff

/--
theorem `mk_coe_finset` / 定理 `mk_coe_finset`

English:
theorem mk_coe_finset
  given: {α : Type u} {s : Finset α}
  statement: #s = ↑(Finset.card s)
  proof: by simp

中文:
定理 mk_coe_finset
  条件: {α : 类型u} {s : Finset α}
  结论: #s = ↑(Finset.card s)
  证明: by simp
-/
theorem mk_coe_finset {α : Type u} {s : Finset α} : #s = ↑(Finset.card s) := by simp

/--
theorem `card_le_of_finset` / 定理 `card_le_of_finset`

English:
theorem card_le_of_finset
  given: {α} (s : Finset α)
  statement: (s.card : Cardinal) <= #α
  proof: @mk_coe_finset _ s ▸ mk_set_le _

中文:
定理 card_le_of_finset
  条件: {α} (s : Finset α)
  结论: (s.card : Cardinal) <= #α
  证明: @mk_coe_finset _ s ▸ mk_set_le _

Depends on / 依赖: mk_coe_finset, mk_set_le
-/
theorem card_le_of_finset {α} (s : Finset α) : (s.card : Cardinal) <= #α :=
  @mk_coe_finset _ s ▸ mk_set_le _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CharZero Cardinal
  body: by
  refine ⟨fun a b h => ?_⟩
  rwa [← lift_mk_fin, ← lift_mk_fin, lift_inj, Cardinal.eq, ← Fintype.card_eq,
    Fintype.card_fin, Fintype.card_fin] at h

中文:
实例 :
  签名: CharZero Cardinal
  定义体: by
  refine ⟨fun a b h => ?_⟩
  rwa [← lift_mk_fin, ← lift_mk_fin, lift_inj, Cardinal.eq, ← Fintype.card_eq,
    Fintype.card_fin, Fintype.card_fin] at h

Depends on / 依赖: Cardinal, Cardinal.eq, Fintype, Fintype.card_eq, Fintype.card_fin, card_eq, card_fin, lift_inj, lift_mk_fin
-/
instance : CharZero Cardinal := by
  refine ⟨fun a b h => ?_⟩
  rwa [← lift_mk_fin, ← lift_mk_fin, lift_inj, Cardinal.eq, ← Fintype.card_eq,
    Fintype.card_fin, Fintype.card_fin] at h

end Cardinal
