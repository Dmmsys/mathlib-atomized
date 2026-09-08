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

/-- We define the order on cardinal numbers by `#α ≤ #β` if and only if
  there exists an embedding (injective function) from α to β. -/
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define the order on cardinal numbers by `#α ≤ #β` if and only if
  there exists an embedding (injective function) from α to β.
-/
instance : LE Cardinal.{u} :=
  ⟨fun q₁ q₂ =>
    Quotient.liftOn₂ q₁ q₂ (fun α β => Nonempty <| α ↪ β) fun _ _ _ _ ⟨e₁⟩ ⟨e₂⟩ =>
      propext ⟨fun ⟨e⟩ => ⟨e.congr e₁ e₂⟩, fun ⟨e⟩ => ⟨e.congr e₁.symm e₂.symm⟩⟩⟩
/-
**Cardinal.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：partialOrder : PartialOrder Cardinal.{u} where le_refl
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**Cardinal.linearOrder** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：linearOrder : LinearOrder Cardinal.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance linearOrder : LinearOrder Cardinal.{u} :=
  { Cardinal.partialOrder with
    le_total := by
      rintro ⟨α⟩ ⟨β⟩
      apply Embedding.total
    toDecidableLE := Classical.decRel _ }
/-
**Cardinal.le_def** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：le_def (α β : Type u) : #α <= #β ↔ Nonempty (α ↪ β)
参数：α β : Type u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def (α β : Type u) : #α ≤ #β ↔ Nonempty (α ↪ β) :=
  Iff.rfl
/-
**Cardinal.mk_le_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_le_of_injective {α β : Type u} {f : α -> β} (hf : Injective f) : #α <= 
#β
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_le_of_injective {α β : Type u} {f : α → β} (hf : Injective f) : #α ≤ #β :=
  ⟨⟨f, hf⟩⟩
/-
**Cardinal._root_.Function.Embedding.cardinal_le** 是 Mathlib 中的一个定理，位于命名空间 `Card
inal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Embedding.cardinal_le {α β : Type u} (f : α ↪ β) : #α ≤ #β :=
  ⟨f⟩
/-
**Cardinal.mk_le_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_le_of_surjective {α β : Type u} {f : α -> β} (hf : Surjective f) : #β <
= #α
参数：hf : Surjective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_le_of_surjective {α β : Type u} {f : α → β} (hf : Surjective f) : #β ≤ #α :=
  ⟨Embedding.ofSurjective f hf⟩
/-
**Cardinal.le_mk_iff_exists_set** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：le_mk_iff_exists_set {c : Cardinal} {α : Type u} : c <= #α ↔ exists p : Se
t α, #p = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem le_mk_iff_exists_set {c : Cardinal} {α : Type u} : c ≤ #α ↔ ∃ p : Set α, #p = c :=
  ⟨inductionOn c fun _ ⟨⟨f, hf⟩⟩ => ⟨Set.range f, (Equiv.ofInjective f hf).cardinal_eq.symm⟩,
    fun ⟨_, e⟩ => e ▸ ⟨⟨Subtype.val, fun _ _ => Subtype.ext⟩⟩⟩
/-
**Cardinal.mk_subtype_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_subtype_le {α : Type u} (p : α -> Prop) : #(Subtype p) <= #α
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_subtype_le {α : Type u} (p : α → Prop) : #(Subtype p) ≤ #α :=
  ⟨Embedding.subtype p⟩
/-
**Cardinal.mk_set_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_set_le (s : Set α) : #s <= #α
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_subtype_le`：mk_subtype_le {α : Type u} (p : α -> Prop) : #(S
ubtype p) <= #α
-/
theorem mk_set_le (s : Set α) : #s ≤ #α :=
  mk_subtype_le (· ∈ s)
/-
**Cardinal.out_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：out_embedding {c c' : Cardinal} : c <= c' ↔ Nonempty (c.out ↪ c'.out)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_out`：mk_out (c : Cardinal) : #c.out = c
· 使用定理 `Cardinal.le_def`：le_def (α β : Type u) : #α <= #β ↔ Nonempty (α ↪ β)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem out_embedding {c c' : Cardinal} : c ≤ c' ↔ Nonempty (c.out ↪ c'.out) := by
  conv_lhs => rw [← Cardinal.mk_out c, ← Cardinal.mk_out c', le_def]
/-
**Cardinal.lift_mk_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_mk_le {α : Type v} {β : Type w} : lift.{max u w} #α <= lift.{max u v}
 #β ↔ Nonempty (α ↪ β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem lift_mk_le {α : Type v} {β : Type w} :
    lift.{max u w} #α ≤ lift.{max u v} #β ↔ Nonempty (α ↪ β) :=
  ⟨fun ⟨f⟩ => ⟨Embedding.congr Equiv.ulift Equiv.ulift f⟩, fun ⟨f⟩ =>
    ⟨Embedding.congr Equiv.ulift.symm Equiv.ulift.symm f⟩⟩

/-- A variant of `Cardinal.lift_mk_le` with specialized universes.
Because Lean often cannot realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
/-
**Cardinal.lift_mk_le'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #α <= lift.{u} #β ↔ Nonem
pty (α ↪ β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_mk_le`：lift_mk_le {α : Type v} {β : Type w} : lift.{max u 
w} #α <= lift.{max u v} #β ↔ Nonempty (α ↪ β)

--- 原说明 ---
A variant of `Cardinal.lift_mk_le` with specialized universes.
Because Lean often cannot realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specializati
on problem either.
-/
theorem lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #α ≤ lift.{u} #β ↔ Nonempty (α ↪ β) :=
  lift_mk_le.{0}

/-! ### `lift` sends `Cardinal.{u}` to an initial segment of `Cardinal.{max u v}`. -/

/-- `Cardinal.lift` as an `InitialSeg`. -/
@[simps!]
/-
**Cardinal.liftInitialSeg** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：liftInitialSeg : Cardinal.{u} <=i Cardinal.{max u v}
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Cardinal.lift` as an `InitialSeg`.
-/
def liftInitialSeg : Cardinal.{u} ≤i Cardinal.{max u v} := by
  refine ⟨(OrderEmbedding.ofMapLEIff lift ?_).ltEmbedding, ?_⟩ <;> intro a b
  · refine inductionOn₂ a b fun _ _ ↦ ?_
    rw [← lift_umax, lift_mk_le.{v, u, u}, le_def]
  · refine inductionOn₂ a b fun α β h ↦ ?_
    obtain ⟨e⟩ := h.le
    replace e := e.congr (Equiv.refl β) Equiv.ulift
    refine ⟨#(range e), mk_congr (Equiv.ulift.trans <| Equiv.symm ?_)⟩
    apply (e.codRestrict _ mem_range_self).equivOfSurjective
    rintro ⟨a, ⟨b, rfl⟩⟩
    exact ⟨b, rfl⟩
/-
**Cardinal.mem_range_lift_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mem_range_lift_of_le {a : Cardinal.{u}} {b : Cardinal.{max u v}} : b <= li
ft.{v, u} a -> b in Set.range lift.{v, u}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.mem_range_of_le`：mem_range_of_le [LT α] (f : α <=i β) (h : b 
<= f a) : b in Set.range f
-/
theorem mem_range_lift_of_le {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b ≤ lift.{v, u} a → b ∈ Set.range lift.{v, u} :=
  liftInitialSeg.mem_range_of_le
/-
**Cardinal.lift_injective** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_injective : Injective lift.{u, v}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
-/
theorem lift_injective : Injective lift.{u, v} :=
  liftInitialSeg.injective

@[simp]
/-
**Cardinal.lift_inj** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.{v, u} b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Cardinal.lift_injective`：lift_injective : Injective lift.{u, v}
-/
theorem lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.{v, u} b ↔ a = b :=
  lift_injective.eq_iff

@[simp]
/-
**Cardinal.lift_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.le_iff_le`：le_iff_le [PartialOrder α] (f : α <=i β) : f a <= 
f a' ↔ a <= a'
-/
theorem lift_le {a b : Cardinal.{v}} : lift.{u} a ≤ lift.{u} b ↔ a ≤ b :=
  liftInitialSeg.le_iff_le

@[simp]
/-
**Cardinal.lift_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v, u} b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.lt_iff_lt`：lt_iff_lt [PartialOrder α] (f : α <=i β) : f a < f
 a' ↔ a < a'
-/
theorem lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v, u} b ↔ a < b :=
  liftInitialSeg.lt_iff_lt
/-
**Cardinal.lift_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_strictMono : StrictMono lift
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
-/
theorem lift_strictMono : StrictMono lift := fun _ _ => lift_lt.2
/-
**Cardinal.lift_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_monotone : Monotone lift
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Cardinal.lift_strictMono`：lift_strictMono : StrictMono lift
-/
theorem lift_monotone : Monotone lift :=
  lift_strictMono.monotone

@[simp]
/-
**Cardinal.lift_min** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_min {a b : Cardinal} : lift.{u, v} (min a b) = min (lift.{u, v} a) (l
ift.{u, v} b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `Cardinal.lift_monotone`：lift_monotone : Monotone lift
-/
theorem lift_min {a b : Cardinal} : lift.{u, v} (min a b) = min (lift.{u, v} a) (lift.{u, v} b) :=
  lift_monotone.map_min

@[simp]
/-
**Cardinal.lift_max** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_max {a b : Cardinal} : lift.{u, v} (max a b) = max (lift.{u, v} a) (l
ift.{u, v} b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `Cardinal.lift_monotone`：lift_monotone : Monotone lift
-/
theorem lift_max {a b : Cardinal} : lift.{u, v} (max a b) = max (lift.{u, v} a) (lift.{u, v} b) :=
  lift_monotone.map_max

-- This cannot be a `@[simp]` lemma because `simp` can't figure out the universes.
/-
**Cardinal.lift_umax_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_umax_eq {a : Cardinal.{u}} {b : Cardinal.{v}} : lift.{max v w} a = li
ft.{max u w} b ↔ lift.{v} a = lift.{u} b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lift_umax_eq {a : Cardinal.{u}} {b : Cardinal.{v}} :
    lift.{max v w} a = lift.{max u w} b ↔ lift.{v} a = lift.{u} b := by
  rw [← lift_lift.{v, w, u}, ← lift_lift.{u, w, v}, lift_inj]
/-
**Cardinal.le_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：le_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} : b <= lift.{v, u}
 a ↔ exists a' <= a, lift.{v, u} a' = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.le_apply_iff`：le_apply_iff [PartialOrder α] (f : α <=i β) : b
 <= f a ↔ exists c <= a, f c = b
-/
theorem le_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b ≤ lift.{v, u} a ↔ ∃ a' ≤ a, lift.{v, u} a' = b :=
  liftInitialSeg.le_apply_iff
/-
**Cardinal.lt_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lt_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} : b < lift.{v, u} 
a ↔ exists a' < a, lift.{v, u} a' = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.lt_apply_iff`：lt_apply_iff [PartialOrder α] (f : α <=i β) : b
 < f a ↔ exists a' < a, f a' = b
-/
theorem lt_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b < lift.{v, u} a ↔ ∃ a' < a, lift.{v, u} a' = b :=
  liftInitialSeg.lt_apply_iff

/-! ### Basic cardinals -/

@[simp]
/-
**Cardinal.lift_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_eq_zero {a : Cardinal.{v}} : lift.{u} a = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Cardinal.lift_injective`：lift_injective : Injective lift.{u, v}
· 使用定理 `Cardinal.lift_zero`：lift_zero : lift 0 = 0

--- 原说明 ---
### Basic cardinals
-/
theorem lift_eq_zero {a : Cardinal.{v}} : lift.{u} a = 0 ↔ a = 0 :=
  lift_injective.eq_iff' lift_zero

@[simp]
/-
**Cardinal.mk_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_fintype (α : Type u) [h : Fintype α] : #α = Fintype.card α
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_ulift`：Fintype.card_ulift (α : Type*) [Fintype α] : Fintype
.card (ULift α) = Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_fintype (α : Type u) [h : Fintype α] : #α = Fintype.card α :=
  mk_congr (Fintype.equivOfCardEq (by simp))

set_option backward.privateInPublic true in
/-
**Cardinal.cast_succ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem cast_succ (n : ℕ) : ((n + 1 : ℕ) : Cardinal.{u}) = n + 1 := by
  change #(ULift.{u} _) = #(ULift.{u} _) + 1
  rw [← mk_option]
  simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Cardinal.commSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：commSemiring : CommSemiring Cardinal.{u} where zero_add a
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.power_zero`：power_zero (a : Cardinal) : a ^ (0 : Cardinal) = 1
· 使用定理 `_private.Mathlib.SetTheory.Cardinal.Order.0.Cardinal.cast_succ`：∀ (n : ℕ
), ↑(n + 1) = ↑n + 1
-/
instance commSemiring : CommSemiring Cardinal.{u} where
  zero_add a := inductionOn a fun α => mk_congr <| Equiv.emptySum _ α
  add_zero a := inductionOn a fun α => mk_congr <| Equiv.sumEmpty α _
  add_assoc a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.sumAssoc α β γ
  add_comm a b := inductionOn₂ a b fun α β => mk_congr <| Equiv.sumComm α β
  zero_mul a := inductionOn a fun _ => mk_eq_zero _
  mul_zero a := inductionOn a fun _ => mk_eq_zero _
  one_mul a := inductionOn a fun α => mk_congr <| Equiv.uniqueProd α _
  mul_one a := inductionOn a fun α => mk_congr <| Equiv.prodUnique α _
  mul_assoc a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.prodAssoc α β γ
  mul_comm a b := inductionOn₂ a b fun α β => mk_congr <| Equiv.prodComm α β
  left_distrib a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.prodSumDistrib α β γ
  right_distrib a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.sumProdDistrib α β γ
  nsmul := nsmulRec
  npow n c := c ^ (n : Cardinal)
  npow_zero := power_zero
  npow_succ n c := by simp_rw [HPow.hPow, Pow.pow]; rw [cast_succ, power_add, power_one]
  natCast n := lift #(Fin n)
  natCast_zero := rfl
  natCast_succ n := cast_succ n
/-
**Cardinal.mk_bool** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_bool : #Bool = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_bool : #Bool = 2 := by simp
/-
**Cardinal.mk_Prop** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_Prop : #Prop = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_Prop : #Prop = 2 := by simp
/-
**Cardinal.power_mul** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_mul {a b c : Cardinal} : a ^ (b * c) = (a ^ b) ^ c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Cardinal.inductionOn₃`：inductionOn₃ {motive : Cardinal -> Cardinal -> Ca
rdinal -> Prop} (c₁ c₂ c₃ : Cardinal) (mk : forall α β γ, motive #α #β #γ) : mot
ive c₁ c₂ c…
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
-/
theorem power_mul {a b c : Cardinal} : a ^ (b * c) = (a ^ b) ^ c := by
  rw [mul_comm b c]
  exact inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.curry γ β α

@[simp, norm_cast]
/-
**Cardinal.power_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_natCast (a : Cardinal.{u}) (n : Nat) : a ^ (↑n : Cardinal.{u}) = a ^
 n
参数：a : Cardinal.{u}；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem power_natCast (a : Cardinal.{u}) (n : ℕ) : a ^ (↑n : Cardinal.{u}) = a ^ n :=
  rfl

@[simp]
/-
**Cardinal.lift_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_eq_one {a : Cardinal.{v}} : lift.{u} a = 1 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Cardinal.lift_injective`：lift_injective : Injective lift.{u, v}
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
-/
theorem lift_eq_one {a : Cardinal.{v}} : lift.{u} a = 1 ↔ a = 1 :=
  lift_injective.eq_iff' lift_one

@[simp]
/-
**Cardinal.lift_mul** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_mul (a b : Cardinal.{u}) : lift.{v} (a * b) = lift.{v} a * lift.{v} b
参数：a b : Cardinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn₂`：inductionOn₂ {motive : Cardinal -> Cardinal -> Pr
op} (c₁ c₂ : Cardinal) (mk : forall α β, motive #α #β) : motive c₁ c₂
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem lift_mul (a b : Cardinal.{u}) : lift.{v} (a * b) = lift.{v} a * lift.{v} b :=
  inductionOn₂ a b fun _ _ =>
    mk_congr <| Equiv.ulift.trans (Equiv.prodCongr Equiv.ulift Equiv.ulift).symm
/-
**Cardinal.lift_two** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_two : lift.{u, v} 2 = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_add`：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = li
ft.{v} a + lift.{v} b
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_two : lift.{u, v} 2 = 2 := by simp [← one_add_one_eq_two]

@[simp]
/-
**Cardinal.mk_set** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_set {α : Type u} : #(Set α) = 2 ^ #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Set.ofPred_bijective`：ofPred_bijective : Bijective (ofPred : (α -> Prop)
 -> Set α)
· 使用定理 `Cardinal.mk_pi`：mk_pi {ι : Type u} (α : ι -> Type v) : #(Π i, α i) = pro
d fun i => #(α i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Cardinal.prod_const`：prod_const (ι : Type u) (a : Cardinal.{v}) : (prod 
fun _ : ι => a) = lift.{u} a ^ lift.{v} #ι
· 使用定理 `Cardinal.lift_add`：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = li
ft.{v} a + lift.{v} b
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_set {α : Type u} : #(Set α) = 2 ^ #α := by
  simp [← mk_congr (Equiv.ofBijective _ Set.ofPred_bijective), ← one_add_one_eq_two]

/-- A variant of `Cardinal.mk_set` expressed in terms of a `Set` instead of a `Type`. -/
@[simp]
/-
**Cardinal.mk_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_powerset {α : Type u} (s : Set α) : #(↥(𝒫 s)) = 2 ^ #(↥s)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Cardinal.mk_set`：mk_set {α : Type u} : #(Set α) = 2 ^ #α

--- 原说明 ---
A variant of `Cardinal.mk_set` expressed in terms of a `Set` instead of a `Type`
.
-/
theorem mk_powerset {α : Type u} (s : Set α) : #(↥(𝒫 s)) = 2 ^ #(↥s) :=
  (mk_congr (Equiv.Set.powerset s)).trans mk_set
/-
**Cardinal.lift_two_power** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_two_power (a : Cardinal) : lift.{v} (2 ^ a) = 2 ^ lift.{v} a
参数：a : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.lift_power`：lift_power (a b : Cardinal.{u}) : lift.{v} (a ^ b) 
= lift.{v} a ^ lift.{v} b
· 使用定理 `Cardinal.lift_add`：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = li
ft.{v} a + lift.{v} b
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_two_power (a : Cardinal) : lift.{v} (2 ^ a) = 2 ^ lift.{v} a := by
  simp [← one_add_one_eq_two]

/-! ### Order properties -/

/-
**Cardinal.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：orderBot : OrderBot Cardinal.{u} where bot
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Order properties
-/
instance orderBot : OrderBot Cardinal.{u} where
  bot := 0
  bot_le := by rintro ⟨α⟩; exact ⟨Embedding.ofIsEmpty⟩
/-
**Cardinal.add_le_add'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem add_le_add' : ∀ {a b c d : Cardinal}, a ≤ b → c ≤ d → a + c ≤ b + d := by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨δ⟩ ⟨e₁⟩ ⟨e₂⟩; exact ⟨e₁.sumMap e₂⟩
/-
**Cardinal.addLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：addLeftMono : AddLeftMono Cardinal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.SetTheory.Cardinal.Order.0.Cardinal.add_le_add'`：∀ {a b
 c d : Cardinal.{u_1}}, a ≤ b → c ≤ d → a + c ≤ b + d
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
instance addLeftMono : AddLeftMono Cardinal :=
  ⟨fun _ _ _ => add_le_add' le_rfl⟩
/-
**Cardinal.addRightMono** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：addRightMono : AddRightMono Cardinal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.SetTheory.Cardinal.Order.0.Cardinal.add_le_add'`：∀ {a b
 c d : Cardinal.{u_1}}, a ≤ b → c ≤ d → a + c ≤ b + d
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
instance addRightMono : AddRightMono Cardinal :=
  ⟨fun _ _ _ h => add_le_add' h le_rfl⟩
/-
**Cardinal.canonicallyOrderedAdd** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：canonicallyOrderedAdd : CanonicallyOrderedAdd Cardinal.{u} where exists_ad
d_of_le {a b}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn₂`：inductionOn₂ {motive : Cardinal -> Cardinal -> Pr
op} (c₁ c₂ : Cardinal) (mk : forall α β, motive #α #β) : motive c₁ c₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_left_mono`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [Ad
dRightMono α] {a : α}, Monotone fun x => x + a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_right_mono`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [A
ddLeftMono α] {a : α}, Monotone fun x => a + x
-/
instance canonicallyOrderedAdd : CanonicallyOrderedAdd Cardinal.{u} where
  exists_add_of_le {a b} :=
    inductionOn₂ a b fun α β ⟨⟨f, hf⟩⟩ =>
      have : α ⊕ ((range f)ᶜ : Set β) ≃ β := by
        classical
        exact (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl _)).trans <|
          Equiv.Set.sumCompl (range f)
      ⟨#(↥(range f)ᶜ), mk_congr this.symm⟩
  le_self_add a b := (add_zero a).ge.trans <| add_right_mono bot_le
  le_add_self a b := (zero_add a).ge.trans <| add_left_mono bot_le

@[deprecated zero_le (since := "2026-04-17")]
/-
**Cardinal.zero_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ (a : Cardinal.{u_1}), 0 ≤ a
参数：a : Cardinal.{u_1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
protected theorem zero_le (a : Cardinal) : 0 ≤ a := zero_le
/-
**Cardinal.isOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：isOrderedRing : IsOrderedRing Cardinal.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CanonicallyOrderedAdd.toIsOrderedRing`：toIsOrderedRing : IsOrderedRing R
 where add_le_add_left _ _
-/
instance isOrderedRing : IsOrderedRing Cardinal.{u} :=
  CanonicallyOrderedAdd.toIsOrderedRing
/-
**Cardinal.noZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：noZeroDivisors : NoZeroDivisors Cardinal.{u} where eq_zero_or_eq_zero_of_m
ul_eq_zero
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn₂`：inductionOn₂ {motive : Cardinal -> Cardinal -> Pr
op} (c₁ c₂ : Cardinal) (mk : forall α β, motive #α #β) : motive c₁ c₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance noZeroDivisors : NoZeroDivisors Cardinal.{u} where
  eq_zero_or_eq_zero_of_mul_eq_zero := fun {a b} =>
    inductionOn₂ a b fun α β => by
      simpa only [mul_def, mk_eq_zero_iff, isEmpty_prod] using id

-- Computable instance to prevent a non-computable one being found via the one above
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommMonoidWithZero Cardinal.{u} :=
  { Cardinal.commSemiring with }

-- Computable instance to prevent a non-computable one being found via the one above
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommMonoid Cardinal.{u} :=
  { Cardinal.commSemiring with }
/-
**Cardinal.zero_power_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：zero_power_le (c : Cardinal.{u}) : (0 : Cardinal.{u}) ^ c <= 1
参数：c : Cardinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.power_zero`：power_zero (a : Cardinal) : a ^ (0 : Cardinal) = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Cardinal.zero_power`：zero_power {a : Cardinal} : a != 0 -> (0 : Cardinal
) ^ a = 0
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem zero_power_le (c : Cardinal.{u}) : (0 : Cardinal.{u}) ^ c ≤ 1 := by
  by_cases h : c = 0
  · rw [h, power_zero]
  · rw [zero_power h]
    apply zero_le
/-
**Cardinal.power_le_power_left** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_le_power_left : forall {a b c : Cardinal}, a != 0 -> b <= c -> a ^ b
 <= a ^ c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.mk_ne_zero_iff`：mk_ne_zero_iff {α : Type u} : #α != 0 ↔ Nonempt
y α
-/
theorem power_le_power_left : ∀ {a b c : Cardinal}, a ≠ 0 → b ≤ c → a ^ b ≤ a ^ c := by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ hα ⟨e⟩
  let ⟨a⟩ := mk_ne_zero_iff.1 hα
  exact ⟨@Function.Embedding.arrowCongrLeft _ _ _ ⟨a⟩ e⟩
/-
**Cardinal.self_le_power** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：self_le_power (a : Cardinal) {b : Cardinal} (hb : 1 <= b) : a <= a ^ b
参数：a : Cardinal；hb : 1 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Cardinal.power_one`：power_one (a : Cardinal.{u}) : a ^ (1 : Cardinal) = 
a
· 使用定理 `Cardinal.power_le_power_left`：power_le_power_left : forall {a b c : Card
inal}, a != 0 -> b <= c -> a ^ b <= a ^ c
-/
theorem self_le_power (a : Cardinal) {b : Cardinal} (hb : 1 ≤ b) : a ≤ a ^ b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact zero_le
  · convert! power_le_power_left ha hb
    exact (power_one a).symm

/-- **Cantor's theorem** -/
/-
**Cardinal.cantor** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：cantor (a : Cardinal.{u}) : a < 2 ^ a
参数：a : Cardinal.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_set`：mk_set {α : Type u} : #(Set α) = 2 ^ #α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.singleton_eq_singleton_iff`：singleton_eq_singleton_iff {x y : α} : {
x} = ({y} : Set α) ↔ x = y
· 使用定理 `Function.cantor_injective`：∀ {α : Type u_4} (f : Set α → α), ¬Function.I
njective f

--- 原说明 ---
**Cantor's theorem**
-/
theorem cantor (a : Cardinal.{u}) : a < 2 ^ a := by
  induction a using Cardinal.inductionOn with | _ α
  rw [← mk_set]
  refine ⟨⟨⟨singleton, fun a b => singleton_eq_singleton_iff.1⟩⟩, ?_⟩
  rintro ⟨⟨f, hf⟩⟩
  exact cantor_injective f hf
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoMaxOrder Cardinal.{u} where exists_gt a := ⟨_, cantor a⟩

-- short-circuit type class inference
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribLattice Cardinal.{u} := inferInstance
/-
**Cardinal.power_le_max_power_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_le_max_power_one {a b c : Cardinal} (h : b <= c) : a ^ b <= max (a ^
 c) 1
参数：h : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.power_le_power_left`：power_le_power_left : forall {a b c : Card
inal}, a != 0 -> b <= c -> a ^ b <= a ^ c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem power_le_max_power_one {a b c : Cardinal} (h : b ≤ c) : a ^ b ≤ max (a ^ c) 1 := by
  by_cases ha : a = 0
  · simp [ha, zero_power_le]
  · exact (power_le_power_left ha h).trans (le_max_left _ _)
/-
**Cardinal.power_le_power_right** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_le_power_right {a b c : Cardinal} : a <= b -> a ^ c <= b ^ c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn₃`：inductionOn₃ {motive : Cardinal -> Cardinal -> Ca
rdinal -> Prop} (c₁ c₂ c₃ : Cardinal) (mk : forall α β γ, motive #α #β #γ) : mot
ive c₁ c₂ c…
-/
theorem power_le_power_right {a b c : Cardinal} : a ≤ b → a ^ c ≤ b ^ c :=
  inductionOn₃ a b c fun _ _ _ ⟨e⟩ => ⟨Embedding.arrowCongrRight e⟩
/-
**Cardinal.power_pos** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_pos {a : Cardinal} (b : Cardinal) (ha : 0 < a) : 0 < a ^ b
参数：b : Cardinal；ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Cardinal.power_ne_zero`：power_ne_zero {a : Cardinal} (b : Cardinal) : a 
!= 0 -> a ^ b != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem power_pos {a : Cardinal} (b : Cardinal) (ha : 0 < a) : 0 < a ^ b :=
  (power_ne_zero _ ha.ne').bot_lt
/-
**Cardinal.lt_wf** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：WellFounded fun x1 x2 => x1 < x2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `Function.Embedding.min_injective`：min_injective [I : Nonempty ι] : exist
s i, Nonempty (forall j, β i ↪ β j)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_out`：mk_out (c : Cardinal) : #c.out = c
-/
protected theorem lt_wf : @WellFounded Cardinal.{u} (· < ·) :=
  ⟨fun a =>
    by_contradiction fun h => by
      let ι := { c : Cardinal // ¬Acc (· < ·) c }
      let f : ι → Cardinal := Subtype.val
      have hι : Nonempty ι := ⟨⟨_, h⟩⟩
      obtain ⟨⟨c : Cardinal, hc : ¬Acc (· < ·) c⟩, ⟨h_1 : ∀ j, (f ⟨c, hc⟩).out ↪ (f j).out⟩⟩ :=
        Embedding.min_injective fun i => (f i).out
      refine hc (Acc.intro _ fun j h' => by_contradiction fun hj => h'.2 ?_)
      have : #_ ≤ #_ := ⟨h_1 ⟨j, hj⟩⟩
      simpa only [mk_out] using this⟩
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WellFoundedRelation Cardinal.{u} :=
  ⟨(· < ·), Cardinal.lt_wf⟩
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WellFoundedLT Cardinal.{u} :=
  ⟨Cardinal.lt_wf⟩
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConditionallyCompleteLinearOrderBot Cardinal :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

@[simp]
/-
**Cardinal.sInf_empty** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sInf_empty : sInf (∅ : Set Cardinal.{u}) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Set.not_nonempty_empty`：not_nonempty_empty : ¬(∅ : Set α).Nonempty
· 使用定理 `Cardinal.instWellFoundedLT`：WellFoundedLT Cardinal.{u}
-/
theorem sInf_empty : sInf (∅ : Set Cardinal.{u}) = 0 :=
  dif_neg Set.not_nonempty_empty

/-- Note that the successor of `c` is not the same as `c + 1` except in the case of finite `c`. -/
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that the successor of `c` is not the same as `c + 1` except in the case of 
finite `c`.
-/
@[no_expose] instance : SuccOrder Cardinal := .ofLinearWellFoundedLT _

@[deprecated Order.succ_eq_csInf (since := "2026-03-21")]
/-
**Cardinal.succ_def** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：succ_def (c : Cardinal) : succ c = sInf { c' | c < c' }
参数：c : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.succ_eq_csInf`：succ_eq_csInf [ConditionallyCompleteLattice α] [Suc
cOrder α] [NoMaxOrder α] (a : α) : succ a = sInf (Set.Ioi a)
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}

--- 原说明 ---
Note that the successor of `c` is not the same as `c + 1` except in the case of 
finite `c`.
-/
theorem succ_def (c : Cardinal) : succ c = sInf { c' | c < c' } :=
  Order.succ_eq_csInf c
/-
**Cardinal.succ_pos** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：succ_pos : forall c : Cardinal, 0 < succ c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem succ_pos : ∀ c : Cardinal, 0 < succ c := by simp

@[simp]
/-
**Cardinal.succ_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：succ_ne_zero (c : Cardinal) : succ c != 0
参数：c : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Cardinal.succ_pos`：succ_pos : forall c : Cardinal, 0 < succ c
-/
theorem succ_ne_zero (c : Cardinal) : succ c ≠ 0 :=
  (succ_pos _).ne'
/-
**Cardinal.add_one_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_one_le_of_lt {a b : Cardinal} (h : a < b) : a + 1 <= b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn₂`：inductionOn₂ {motive : Cardinal -> Cardinal -> Pr
op} (c₁ c₂ : Cardinal) (mk : forall α β, motive #α #β) : motive c₁ c₂
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Cardinal.mk_le_of_surjective`：mk_le_of_surjective {α β : Type u} {f : α 
-> β} (hf : Surjective f) : #β <= #α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Function.Surjective.eq_1`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), F
unction.Surjective f = ∀ (b : β), ∃ a, f a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_option`：mk_option {α : Type u} : #(Option α) = #α + 1
· 使用定理 `Function.Embedding.cardinal_le`：∀ {α β : Type u} (f : α ↪ β), Cardinal.m
k α ≤ Cardinal.mk β
-/
theorem add_one_le_of_lt {a b : Cardinal} (h : a < b) : a + 1 ≤ b := by
  induction a, b using Cardinal.inductionOn₂ with | mk α β
  obtain ⟨f⟩ := h.le
  have hf : ¬Surjective f := fun hn ↦ h.not_ge (mk_le_of_surjective hn)
  rw [Surjective, not_forall] at hf
  obtain ⟨b, hb⟩ := hf
  rw [← mk_option]
  exact (f.optionElim b hb).cardinal_le

@[deprecated add_one_le_of_lt (since := "2026-03-21")]
/-
**Cardinal.add_one_le_succ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_one_le_succ (c : Cardinal) : c + 1 <= succ c
参数：c : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.add_one_le_of_lt`：add_one_le_of_lt {a b : Cardinal} (h : a < b)
 : a + 1 <= b
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
-/
theorem add_one_le_succ (c : Cardinal) : c + 1 ≤ succ c :=
  add_one_le_of_lt (lt_succ c)

@[simp]
/-
**Cardinal.lift_succ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_succ (a) : lift.{v, u} (succ a) = succ (lift.{v, u} a)
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_lift_iff`：lt_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max 
u v}} : b < lift.{v, u} a ↔ exists a' < a, lift.{v, u} a' = b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
-/
theorem lift_succ (a) : lift.{v, u} (succ a) = succ (lift.{v, u} a) := by
  apply (succ_le_of_lt <| lift_lt.2 <| lt_succ a).antisymm'
  by_contra! h
  rcases lt_lift_iff.1 h with ⟨b, h, hb⟩
  rw [lt_succ_iff, ← lift_le, hb] at h
  exact h.not_gt (lt_succ _)

/-! ### Limit cardinals -/

/-
**Cardinal.ne_zero_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ne_zero_of_isSuccLimit {c} (h : IsSuccLimit c) : c != 0
参数：h : IsSuccLimit c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccLimit.ne_bot`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → a ≠ ⊥

--- 原说明 ---
### Limit cardinals
-/
theorem ne_zero_of_isSuccLimit {c} (h : IsSuccLimit c) : c ≠ 0 :=
  h.ne_bot
/-
**Cardinal.isSuccPrelimit_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isSuccPrelimit_zero : IsSuccPrelimit (0 : Cardinal)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isSuccPrelimit_bot`：isSuccPrelimit_bot [OrderBot α] : IsSuccPrelim
it (⊥ : α)
-/
theorem isSuccPrelimit_zero : IsSuccPrelimit (0 : Cardinal) :=
  isSuccPrelimit_bot
/-
**Cardinal.isSuccLimit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u_1}}, Order.IsSuccLimit c ↔ c ≠ 0 ∧ Order.IsSuccPrelimit
 c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isSuccLimit_iff_of_orderBot`：isSuccLimit_iff_of_orderBot [OrderBot
 α] : IsSuccLimit a ↔ a != ⊥ ∧ IsSuccPrelimit a
-/
protected theorem isSuccLimit_iff {c : Cardinal} : IsSuccLimit c ↔ c ≠ 0 ∧ IsSuccPrelimit c :=
  isSuccLimit_iff_of_orderBot

@[simp]
/-
**Cardinal.not_isSuccLimit_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：¬Order.IsSuccLimit 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.not_isSuccLimit_bot`：not_isSuccLimit_bot [OrderBot α] : ¬ IsSuccLi
mit (⊥ : α)
-/
protected theorem not_isSuccLimit_zero : ¬ IsSuccLimit (0 : Cardinal) :=
  not_isSuccLimit_bot

/-- A cardinal is a strong pre-limit if it's closed under powersets.

See `IsStrongLimit` for a version excluding `0`. -/
/-
**Cardinal.IsStrongPrelimit** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：IsStrongPrelimit (c : Cardinal) : Prop
参数：c : Cardinal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cardinal is a strong pre-limit if it's closed under powersets.

See `IsStrongLimit` for a version excluding `0`.
-/
def IsStrongPrelimit (c : Cardinal) : Prop :=
  ∀ ⦃x⦄, x < c → 2 ^ x < c

/-- A cardinal is a strong limit if it is not zero and it is closed under powersets.
Note that `ℵ₀` is a strong limit by this definition.

See `IsStrongPrelimit` for a version including `0`. -/
@[mk_iff]
/-
**Cardinal.IsStrongLimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cardinal`。
形式化陈述：Cardinal.{u_1} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cardinal is a strong limit if it is not zero and it is closed under powersets.
Note that `ℵ₀` is a strong limit by this definition.

See `IsStrongPrelimit` for a version including `0`.
-/
structure IsStrongLimit (c : Cardinal) : Prop where
  ne_zero : c ≠ 0
  protected isStrongPrelimit : IsStrongPrelimit c

@[deprecated (since := "2026-03-31")]
alias IsStrongLimit.two_power_lt := IsStrongLimit.isStrongPrelimit
/-
**Cardinal.IsStrongPrelimit.isSuccPrelimit** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.I
sStrongPrelimit`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsStrongPrelimit → Order.IsSuccPrelimit c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isSuccPrelimit_of_succ_lt`：isSuccPrelimit_of_succ_lt (H : forall a
 < b, succ a < b) : IsSuccPrelimit b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `Cardinal.cantor`：cantor (a : Cardinal.{u}) : a < 2 ^ a
-/
protected theorem IsStrongPrelimit.isSuccPrelimit {c} (hc : IsStrongPrelimit c) :
    IsSuccPrelimit c :=
  isSuccPrelimit_of_succ_lt fun x hx ↦ (succ_le_of_lt <| cantor x).trans_lt (hc hx)
/-
**Cardinal.IsStrongLimit.isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsStron
gLimit`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsStrongLimit → Order.IsSuccLimit c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.isSuccLimit_iff`：∀ {c : Cardinal.{u_1}}, Order.IsSuccLimit c ↔ 
c ≠ 0 ∧ Order.IsSuccPrelimit c
· 使用定理 `Cardinal.IsStrongLimit.ne_zero`：∀ {c : Cardinal.{u_1}}, c.IsStrongLimit 
→ c ≠ 0
· 使用定理 `Cardinal.IsStrongPrelimit.isSuccPrelimit`：∀ {c : Cardinal.{u_1}}, c.IsSt
rongPrelimit → Order.IsSuccPrelimit c
· 使用定理 `Cardinal.IsStrongLimit.isStrongPrelimit`：∀ {c : Cardinal.{u_1}}, c.IsStr
ongLimit → c.IsStrongPrelimit
-/
protected theorem IsStrongLimit.isSuccLimit {c} (hc : IsStrongLimit c) : IsSuccLimit c := by
  rw [Cardinal.isSuccLimit_iff]
  exact ⟨hc.ne_zero, hc.isStrongPrelimit.isSuccPrelimit⟩
/-
**Cardinal.IsStrongLimit.isSuccPrelimit** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsSt
rongLimit`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsStrongLimit → Order.IsSuccPrelimit c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
· 使用定理 `Cardinal.IsStrongLimit.isSuccLimit`：∀ {c : Cardinal.{u_1}}, c.IsStrongLi
mit → Order.IsSuccLimit c
-/
protected theorem IsStrongLimit.isSuccPrelimit {c} (H : IsStrongLimit c) : IsSuccPrelimit c :=
  H.isSuccLimit.isSuccPrelimit
/-
**Cardinal.not_isStrongPrelimit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：not_isStrongPrelimit_iff {c} : ¬ IsStrongPrelimit c ↔ exists x < c, c <= 2
 ^ x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_isStrongPrelimit_iff {c} : ¬ IsStrongPrelimit c ↔ ∃ x < c, c ≤ 2 ^ x := by
  simp [IsStrongPrelimit]

@[simp]
/-
**Cardinal.IsStrongPrelimit.zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsStrongPre
limit`。
形式化陈述：Cardinal.IsStrongPrelimit 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem IsStrongPrelimit.zero : IsStrongPrelimit 0 := by
  simp [IsStrongPrelimit]

@[simp]
/-
**Cardinal.not_isStrongLimit_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：not_isStrongLimit_zero : ¬ IsStrongLimit (0 : Cardinal)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.IsStrongLimit.ne_zero`：∀ {c : Cardinal.{u_1}}, c.IsStrongLimit 
→ c ≠ 0
-/
theorem not_isStrongLimit_zero : ¬ IsStrongLimit (0 : Cardinal) :=
  fun h ↦ h.ne_zero rfl

/-! ### Indexed cardinal `sum` -/

/-
**Cardinal.lift_le_sum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_le_sum {ι : Type u} (f : ι -> Cardinal.{v}) (i) : lift.{u, v} (f i) <
= sum f
参数：f : ι -> Cardinal.{v}；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
### Indexed cardinal `sum`
-/
theorem lift_le_sum {ι : Type u} (f : ι → Cardinal.{v}) (i) : lift.{u, v} (f i) ≤ sum f := by
  rw [← Quotient.out_eq (f i)]
  exact ⟨⟨fun a => ⟨i, a.down⟩, fun a b h => by simpa using h⟩⟩
/-
**Cardinal.le_sum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：le_sum {ι : Type u} (f : ι -> Cardinal.{max u v}) (i) : f i <= sum f
参数：f : ι -> Cardinal.{max u v}；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.lift_le_sum`：lift_le_sum {ι : Type u} (f : ι -> Cardinal.{v}) (
i) : lift.{u, v} (f i) <= sum f
-/
theorem le_sum {ι : Type u} (f : ι → Cardinal.{max u v}) (i) : f i ≤ sum f := by
  simpa [← lift_umax] using lift_le_sum f i
/-
**Cardinal.iSup_le_sum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：iSup_le_sum {ι} (f : ι -> Cardinal) : iSup f <= sum f
参数：f : ι -> Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `Cardinal.le_sum`：le_sum {ι : Type u} (f : ι -> Cardinal.{max u v}) (i) :
 f i <= sum f
-/
theorem iSup_le_sum {ι} (f : ι → Cardinal) : iSup f ≤ sum f :=
  ciSup_le' <| le_sum _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Cardinal.sum_add_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sum_add_distrib {ι} (f g : ι -> Cardinal) : sum (f + g) = sum f + sum g
参数：f g : ι -> Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
· 使用定理 `Cardinal.mk_out`：mk_out (c : Cardinal) : #c.out = c
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem sum_add_distrib {ι} (f g : ι → Cardinal) : sum (f + g) = sum f + sum g := by
  have := mk_congr (Equiv.sigmaSumDistrib (Quotient.out ∘ f) (Quotient.out ∘ g))
  simp only [comp_apply, mk_sigma, mk_sum, mk_out, lift_id] at this
  exact this

@[simp]
/-
**Cardinal.sum_add_distrib'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sum_add_distrib' {ι} (f g : ι -> Cardinal) : (Cardinal.sum fun i => f i + 
g i) = sum f + sum g
参数：f g : ι -> Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.sum_add_distrib`：sum_add_distrib {ι} (f g : ι -> Cardinal) : su
m (f + g) = sum f + sum g
-/
theorem sum_add_distrib' {ι} (f g : ι → Cardinal) :
    (Cardinal.sum fun i => f i + g i) = sum f + sum g :=
  sum_add_distrib f g

@[gcongr]
/-
**Cardinal.sum_le_sum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sum_le_sum {ι} (f g : ι -> Cardinal) (H : forall i, f i <= g i) : sum f <=
 sum g
参数：f g : ι -> Cardinal；H : forall i, f i <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quot.out_eq`：Quot.out_eq {r : α -> α -> Prop} (q : Quot r) : Quot.mk r q
.out = q
-/
theorem sum_le_sum {ι} (f g : ι → Cardinal) (H : ∀ i, f i ≤ g i) : sum f ≤ sum g :=
  ⟨(Embedding.refl _).sigmaMap fun i =>
      Classical.choice <| by have := H i; rwa [← Quot.out_eq (f i), ← Quot.out_eq (g i)] at this⟩
/-
**Cardinal.mk_le_mk_mul_of_mk_preimage_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_le_mk_mul_of_mk_preimage_le {c : Cardinal} (f : α -> β) (hf : forall b 
: β, #(f ⁻¹' {b}) <= c) : #α <= #β * c
参数：f : α -> β；hf : forall b : β, #(f ⁻¹' {b}) <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
· 使用定理 `Cardinal.sum_le_sum`：sum_le_sum {ι} (f g : ι -> Cardinal) (H : forall i,
 f i <= g i) : sum f <= sum g
-/
theorem mk_le_mk_mul_of_mk_preimage_le {c : Cardinal} (f : α → β) (hf : ∀ b : β, #(f ⁻¹' {b}) ≤ c) :
    #α ≤ #β * c := by
  simpa only [← mk_congr (@Equiv.sigmaFiberEquiv α β f), mk_sigma, ← sum_const'] using!
    sum_le_sum _ _ hf
/-
**Cardinal.lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le** 是 Mathlib 中的一个定理，位于命名
空间 `Cardinal`。
形式化陈述：lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le {α : Type u} {β : Type v} {c
 : Cardinal} (f : α -> β) (hf : forall b : β, lift.{v} #(f ⁻¹' {b}) <= c) : lift
.{v} #α <= lift.{u} #β * c
参数：f : α -> β；hf : forall b : β, lift.{v} #(f ⁻¹' {b}) <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_le_mk_mul_of_mk_preimage_le`：mk_le_mk_mul_of_mk_preimage_le 
{c : Cardinal} (f : α -> β) (hf : forall b : β, #(f ⁻¹' {b}) <= c) : #α <= #β * 
c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ULift.forall`：∀ {α : Type u} {p : ULift.{u_1, u} α → Prop}, (∀ (x : ULif
t.{u_1, u} α), p x) ↔ ∀ (x : α), p { down := x }
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le {α : Type u} {β : Type v} {c : Cardinal}
    (f : α → β) (hf : ∀ b : β, lift.{v} #(f ⁻¹' {b}) ≤ c) : lift.{v} #α ≤ lift.{u} #β * c :=
  (mk_le_mk_mul_of_mk_preimage_le fun x : ULift.{v} α => ULift.up.{u} (f x.1)) <|
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
/-
**nonempty_embedding_to_cardinal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_embedding_to_cardinal : Nonempty (α ↪ Cardinal.{u})
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Function.Embedding.total`：total (α : Type u) (β : Type v) : Nonempty (α 
↪ β) ∨ Nonempty (β ↪ α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Function.invFun_surjective`：invFun_surjective (hf : Injective f) : Surje
ctive (invFun f)
· 使用定理 `Cardinal.le_sum`：le_sum {ι : Type u} (f : ι -> Cardinal.{max u v}) (i) :
 f i <= sum f
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.cantor`：cantor (a : Cardinal.{u}) : a < 2 ^ a
-/
theorem nonempty_embedding_to_cardinal : Nonempty (α ↪ Cardinal.{u}) :=
  (Embedding.total _ _).resolve_left fun ⟨⟨f, hf⟩⟩ =>
    let g : α → Cardinal.{u} := invFun f
    let ⟨x, (hx : g x = 2 ^ sum g)⟩ := invFun_surjective hf (2 ^ sum g)
    have : g x ≤ sum g := le_sum.{u, u} g x
    not_le_of_gt (by rw [hx]; exact cantor _) this

/-- An embedding of any type to the set of cardinals in its universe. -/
/-
**embeddingToCardinal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：embeddingToCardinal : α ↪ Cardinal.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_embedding_to_cardinal`：nonempty_embedding_to_cardinal : Nonempt
y (α ↪ Cardinal.{u})

--- 原说明 ---
An embedding of any type to the set of cardinals in its universe.
-/
def embeddingToCardinal : α ↪ Cardinal.{u} :=
  Classical.choice nonempty_embedding_to_cardinal

/-- Any type can be endowed with a well order, obtained by pulling back the well order over
cardinals by some embedding. -/
/-
**WellOrderingRel** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WellOrderingRel : α -> α -> Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any type can be endowed with a well order, obtained by pulling back the well ord
er over
cardinals by some embedding.
-/
def WellOrderingRel : α → α → Prop :=
  embeddingToCardinal ⁻¹'o (· < ·)
/-
**WellOrderingRel.isWellOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WellOrderingRel.isWellOrder : IsWellOrder α WellOrderingRel
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.isWellOrder`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop} (x : r ↪r s) [IsWellOrder β s], IsWellOrder α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Cardinal.instWellFoundedLT`：WellFoundedLT Cardinal.{u}
-/
instance WellOrderingRel.isWellOrder : IsWellOrder α WellOrderingRel :=
  (RelEmbedding.preimage _ _).isWellOrder
/-
**IsWellOrder.subtype_nonempty** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsWellOrder.subtype_nonempty : Nonempty { r // IsWellOrder α r }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsWellOrder.subtype_nonempty : Nonempty { r // IsWellOrder α r } :=
  ⟨⟨WellOrderingRel, inferInstance⟩⟩

variable (α) in
/-- The **well-ordering theorem** (or **Zermelo's theorem**): every type can be well-ordered. -/
/-
**exists_wellFoundedLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_wellFoundedLT : exists (_ : LinearOrder α), WellFoundedLT α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsStrictTotalOrderOfIsWellOrder`：∀ {α : Type u_1} (r : α → α → Prop)
 [IsWellOrder α r], IsStrictTotalOrder α r
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r

--- 原说明 ---
The **well-ordering theorem** (or **Zermelo's theorem**): every type can be well
-ordered.
-/
theorem exists_wellFoundedLT : ∃ (_ : LinearOrder α), WellFoundedLT α := by
  classical
  exact ⟨linearOrderOfSTO WellOrderingRel, ⟨WellOrderingRel.isWellOrder.wf⟩⟩

variable (α) in
/-- The **well-ordering theorem** (or **Zermelo's theorem**): every type can be co-well-ordered. -/
@[to_dual existing]
/-
**exists_wellFoundedGT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_wellFoundedGT : exists (_ : LinearOrder α), WellFoundedGT α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.instIsStrictTotalOrderSwapProp`：∀ {α : Sort u_1} (r : α → α → P
rop) [IsStrictTotalOrder α r], IsStrictTotalOrder α (Function.swap r)
· 使用定理 `instIsStrictTotalOrderOfIsWellOrder`：∀ {α : Type u_1} (r : α → α → Prop)
 [IsWellOrder α r], IsStrictTotalOrder α r
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r

--- 原说明 ---
The **well-ordering theorem** (or **Zermelo's theorem**): every type can be co-w
ell-ordered.
-/
lemma exists_wellFoundedGT : ∃ (_ : LinearOrder α), WellFoundedGT α := by
  classical
  exact ⟨linearOrderOfSTO (Function.swap WellOrderingRel), ⟨WellOrderingRel.isWellOrder.wf⟩⟩

@[deprecated (since := "2026-04-12")] alias exists_wellOrder := exists_wellFoundedLT

namespace Cardinal

@[deprecated exists_eq_ciSup_of_not_isSuccPrelimit (since := "2026-04-13")]
/-
**Cardinal.exists_eq_of_iSup_eq_of_not_isSuccPrelimit** 是 Mathlib 中的一个引理，位于命名空间 
`Cardinal`。
形式化陈述：exists_eq_of_iSup_eq_of_not_isSuccPrelimit {ι : Type u} (f : ι -> Cardinal
.{v}) (ω : Cardinal.{v}) (hω : ¬ IsSuccPrelimit ω) (h : ⨆ i : ι, f i = ω) : exis
ts i, f i = ω
参数：f : ι -> Cardinal.{v}；ω : Cardinal.{v}；hω : ¬ IsSuccPrelimit ω；h : ⨆ i : ι, f
 i = ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_eq_ciSup_of_not_isSuccPrelimit`：exists_eq_ciSup_of_not_isSuccPrel
imit (hf' : ¬ IsSuccPrelimit (⨆ i, f i)) : exists i, f i = ⨆ i, f i
-/
lemma exists_eq_of_iSup_eq_of_not_isSuccPrelimit
    {ι : Type u} (f : ι → Cardinal.{v}) (ω : Cardinal.{v})
    (hω : ¬ IsSuccPrelimit ω)
    (h : ⨆ i : ι, f i = ω) : ∃ i, f i = ω := by
  subst h
  exact exists_eq_ciSup_of_not_isSuccPrelimit hω

@[deprecated exists_eq_ciSup_of_not_isSuccLimit (since := "2026-04-13")]
/-
**Cardinal.exists_eq_of_iSup_eq_of_not_isSuccLimit** 是 Mathlib 中的一个引理，位于命名空间 `Ca
rdinal`。
形式化陈述：exists_eq_of_iSup_eq_of_not_isSuccLimit {ι : Type u} [hι : Nonempty ι] (f 
: ι -> Cardinal.{v}) (hf : BddAbove (range f)) {c : Cardinal.{v}} (hc : ¬ IsSucc
Limit c) (h : ⨆ i, f i = c) : exists i, f i = c
参数：f : ι -> Cardinal.{v}；hf : BddAbove (range f)；hc : ¬ IsSuccLimit c；h : ⨆ i, f
 i = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_eq_ciSup_of_not_isSuccLimit`：exists_eq_ciSup_of_not_isSuccLimit (
hbdd : BddAbove (range f)) (hf : ¬ IsSuccLimit (⨆ i, f i)) : exists i, f i = ⨆ i
, f i
-/
lemma exists_eq_of_iSup_eq_of_not_isSuccLimit
    {ι : Type u} [hι : Nonempty ι] (f : ι → Cardinal.{v}) (hf : BddAbove (range f))
    {c : Cardinal.{v}} (hc : ¬ IsSuccLimit c)
    (h : ⨆ i, f i = c) : ∃ i, f i = c := by
  subst h
  exact exists_eq_ciSup_of_not_isSuccLimit hf hc

/-! ### Indexed cardinal `prod` -/

/-- **König's theorem** -/
/-
**Cardinal.sum_lt_prod** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sum_lt_prod {ι} (f g : ι -> Cardinal) (H : forall i, f i < g i) : sum f < 
prod g
参数：f g : ι -> Cardinal；H : forall i, f i < g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.mk_ne_zero_iff`：mk_ne_zero_iff {α : Type u} : #α != 0 ↔ Nonempt
y α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_out`：mk_out (c : Cardinal) : #c.out = c
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Function.invFun_surjective`：invFun_surjective (hf : Injective f) : Surje
ctive (invFun f)
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
**König's theorem**
-/
theorem sum_lt_prod {ι} (f g : ι → Cardinal) (H : ∀ i, f i < g i) : sum f < prod g :=
  lt_of_not_ge fun ⟨F⟩ => by
    have : Inhabited (∀ i : ι, (g i).out) := by
      refine ⟨fun i => Classical.choice <| mk_ne_zero_iff.1 ?_⟩
      rw [mk_out]
      exact (H i).ne_bot
    let G := invFun F
    have sG : Surjective G := invFun_surjective F.2
    choose C hc using
      show ∀ i, ∃ b, ∀ a, G ⟨i, a⟩ i ≠ b by
        intro i
        simp only [not_exists.symm, not_forall.symm]
        refine fun h => (H i).not_ge ?_
        rw [← mk_out (f i), ← mk_out (g i)]
        exact ⟨Embedding.ofSurjective _ h⟩
    let ⟨⟨i, a⟩, h⟩ := sG C
    exact hc i a (congr_fun h _)
/-
**Cardinal.prod_le_prod** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：prod_le_prod {ι} (f g : ι -> Cardinal) (H : forall i, f i <= g i) : prod f
 <= prod g
参数：f g : ι -> Cardinal；H : forall i, f i <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_out`：mk_out (c : Cardinal) : #c.out = c
-/
theorem prod_le_prod {ι} (f g : ι → Cardinal) (H : ∀ i, f i ≤ g i) : prod f ≤ prod g :=
  ⟨Embedding.piCongrRight fun i =>
      Classical.choice <| by have := H i; rwa [← mk_out (f i), ← mk_out (g i)] at this⟩

/-! ### The first infinite cardinal `aleph0` -/

/-
**Cardinal.aleph0_pos** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_pos : 0 < ℵ₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Cardinal.aleph0_ne_zero`：aleph0_ne_zero : ℵ₀ != 0

--- 原说明 ---
### The first infinite cardinal `aleph0`
-/
theorem aleph0_pos : 0 < ℵ₀ :=
  pos_iff_ne_zero.2 aleph0_ne_zero

@[simp]
/-
**Cardinal.aleph0_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_le_lift {c : Cardinal.{u}} : ℵ₀ <= lift.{v} c ↔ ℵ₀ <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
theorem aleph0_le_lift {c : Cardinal.{u}} : ℵ₀ ≤ lift.{v} c ↔ ℵ₀ ≤ c := by
  simpa using lift_le (a := ℵ₀)

@[simp]
/-
**Cardinal.lift_le_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_le_aleph0 {c : Cardinal.{u}} : lift.{v} c <= ℵ₀ ↔ c <= ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
theorem lift_le_aleph0 {c : Cardinal.{u}} : lift.{v} c ≤ ℵ₀ ↔ c ≤ ℵ₀ := by
  simpa using lift_le (b := ℵ₀)

@[simp]
/-
**Cardinal.aleph0_lt_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_lt_lift {c : Cardinal.{u}} : ℵ₀ < lift.{v} c ↔ ℵ₀ < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
-/
theorem aleph0_lt_lift {c : Cardinal.{u}} : ℵ₀ < lift.{v} c ↔ ℵ₀ < c := by
  simpa using lift_lt (a := ℵ₀)

@[simp]
/-
**Cardinal.lift_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_lt_aleph0 {c : Cardinal.{u}} : lift.{v} c < ℵ₀ ↔ c < ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
-/
theorem lift_lt_aleph0 {c : Cardinal.{u}} : lift.{v} c < ℵ₀ ↔ c < ℵ₀ := by
  simpa using lift_lt (b := ℵ₀)

@[simp]
/-
**Cardinal.aleph0_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_eq_lift {c : Cardinal.{u}} : ℵ₀ = lift.{v} c ↔ ℵ₀ = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
-/
theorem aleph0_eq_lift {c : Cardinal.{u}} : ℵ₀ = lift.{v} c ↔ ℵ₀ = c := by
  simpa using lift_inj (a := ℵ₀)

@[simp]
/-
**Cardinal.lift_eq_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_eq_aleph0 {c : Cardinal.{u}} : lift.{v} c = ℵ₀ ↔ c = ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm_eq`：eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lift_eq_aleph0 {c : Cardinal.{u}} : lift.{v} c = ℵ₀ ↔ c = ℵ₀ := by
  simp [eqComm]

/-! ### Properties about the cast from `ℕ` -/

/-
**Cardinal.mk_fin** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_fin (n : Nat) : #(Fin n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Properties about the cast from `ℕ`
-/
theorem mk_fin (n : ℕ) : #(Fin n) = n := by simp

@[simp]
/-
**Cardinal.lift_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{v}) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Cardinal.lift_zero`：lift_zero : lift 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Cardinal.lift_add`：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = li
ft.{v} a + lift.{v} b
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
-/
theorem lift_natCast (n : ℕ) : lift.{u} (n : Cardinal.{v}) = n := by induction n <;> simp [*]

@[simp]
/-
**Cardinal.lift_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_ofNat (n : Nat) [n.AtLeastTwo] : lift.{u} (ofNat(n) : Cardinal.{v}) =
 OfNat.ofNat n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
-/
theorem lift_ofNat (n : ℕ) [n.AtLeastTwo] :
    lift.{u} (ofNat(n) : Cardinal.{v}) = OfNat.ofNat n :=
  lift_natCast n

@[simp]
/-
**Cardinal.lift_eq_nat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_eq_nat_iff {a : Cardinal.{u}} {n : Nat} : lift.{v} a = n ↔ a = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Cardinal.lift_injective`：lift_injective : Injective lift.{u, v}
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
-/
theorem lift_eq_nat_iff {a : Cardinal.{u}} {n : ℕ} : lift.{v} a = n ↔ a = n :=
  lift_injective.eq_iff' (lift_natCast n)

@[simp]
/-
**Cardinal.lift_eq_ofNat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_eq_ofNat_iff {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo] : lift.{v} a
 = ofNat(n) ↔ a = OfNat.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_eq_nat_iff`：lift_eq_nat_iff {a : Cardinal.{u}} {n : Nat} :
 lift.{v} a = n ↔ a = n
-/
theorem lift_eq_ofNat_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    lift.{v} a = ofNat(n) ↔ a = OfNat.ofNat n :=
  lift_eq_nat_iff

@[simp]
/-
**Cardinal.nat_eq_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nat_eq_lift_iff {n : Nat} {a : Cardinal.{u}} : (n : Cardinal) = lift.{v} a
 ↔ (n : Cardinal) = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nat_eq_lift_iff {n : ℕ} {a : Cardinal.{u}} :
    (n : Cardinal) = lift.{v} a ↔ (n : Cardinal) = a := by
  rw [← lift_natCast.{v, u} n, lift_inj]

@[simp]
/-
**Cardinal.zero_eq_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：zero_eq_lift_iff {a : Cardinal.{u}} : (0 : Cardinal) = lift.{v} a ↔ 0 = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm_eq`：eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem zero_eq_lift_iff {a : Cardinal.{u}} :
    (0 : Cardinal) = lift.{v} a ↔ 0 = a := by
  simp [eqComm]

@[simp]
/-
**Cardinal.one_eq_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：one_eq_lift_iff {a : Cardinal.{u}} : (1 : Cardinal) = lift.{v} a ↔ 1 = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm_eq`：eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem one_eq_lift_iff {a : Cardinal.{u}} :
    (1 : Cardinal) = lift.{v} a ↔ 1 = a := by
  simp [eqComm]

@[simp]
/-
**Cardinal.ofNat_eq_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ofNat_eq_lift_iff {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo] : (ofNat(n) 
: Cardinal) = lift.{v} a ↔ (OfNat.ofNat n : Cardinal) = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.nat_eq_lift_iff`：nat_eq_lift_iff {n : Nat} {a : Cardinal.{u}} :
 (n : Cardinal) = lift.{v} a ↔ (n : Cardinal) = a
-/
theorem ofNat_eq_lift_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) = lift.{v} a ↔ (OfNat.ofNat n : Cardinal) = a :=
  nat_eq_lift_iff

@[simp]
/-
**Cardinal.lift_le_nat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_le_nat_iff {a : Cardinal.{u}} {n : Nat} : lift.{v} a <= n ↔ a <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lift_le_nat_iff {a : Cardinal.{u}} {n : ℕ} : lift.{v} a ≤ n ↔ a ≤ n := by
  rw [← lift_natCast.{v, u}, lift_le]

@[simp]
/-
**Cardinal.lift_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_le_one_iff {a : Cardinal.{u}} : lift.{v} a <= 1 ↔ a <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Cardinal.lift_le_nat_iff`：lift_le_nat_iff {a : Cardinal.{u}} {n : Nat} :
 lift.{v} a <= n ↔ a <= n
-/
theorem lift_le_one_iff {a : Cardinal.{u}} :
    lift.{v} a ≤ 1 ↔ a ≤ 1 := by
  simpa using lift_le_nat_iff (n := 1)

@[simp]
/-
**Cardinal.lift_le_ofNat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_le_ofNat_iff {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo] : lift.{v} a
 <= ofNat(n) ↔ a <= OfNat.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_le_nat_iff`：lift_le_nat_iff {a : Cardinal.{u}} {n : Nat} :
 lift.{v} a <= n ↔ a <= n
-/
theorem lift_le_ofNat_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    lift.{v} a ≤ ofNat(n) ↔ a ≤ OfNat.ofNat n :=
  lift_le_nat_iff

@[simp]
/-
**Cardinal.nat_le_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nat_le_lift_iff {n : Nat} {a : Cardinal.{u}} : n <= lift.{v} a ↔ n <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nat_le_lift_iff {n : ℕ} {a : Cardinal.{u}} : n ≤ lift.{v} a ↔ n ≤ a := by
  rw [← lift_natCast.{v, u}, lift_le]

@[simp]
/-
**Cardinal.one_le_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：one_le_lift_iff {a : Cardinal.{u}} : (1 : Cardinal) <= lift.{v} a ↔ 1 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Cardinal.nat_le_lift_iff`：nat_le_lift_iff {n : Nat} {a : Cardinal.{u}} :
 n <= lift.{v} a ↔ n <= a
-/
theorem one_le_lift_iff {a : Cardinal.{u}} :
    (1 : Cardinal) ≤ lift.{v} a ↔ 1 ≤ a := by
  simpa using nat_le_lift_iff (n := 1)

@[simp]
/-
**Cardinal.ofNat_le_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ofNat_le_lift_iff {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo] : (ofNat(n) 
: Cardinal) <= lift.{v} a ↔ (OfNat.ofNat n : Cardinal) <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.nat_le_lift_iff`：nat_le_lift_iff {n : Nat} {a : Cardinal.{u}} :
 n <= lift.{v} a ↔ n <= a
-/
theorem ofNat_le_lift_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) ≤ lift.{v} a ↔ (OfNat.ofNat n : Cardinal) ≤ a :=
  nat_le_lift_iff

@[simp]
/-
**Cardinal.lift_lt_nat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_lt_nat_iff {a : Cardinal.{u}} {n : Nat} : lift.{v} a < n ↔ a < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lift_lt_nat_iff {a : Cardinal.{u}} {n : ℕ} : lift.{v} a < n ↔ a < n := by
  rw [← lift_natCast.{v, u}, lift_lt]

@[simp]
/-
**Cardinal.lift_lt_ofNat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_lt_ofNat_iff {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo] : lift.{v} a
 < ofNat(n) ↔ a < OfNat.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_lt_nat_iff`：lift_lt_nat_iff {a : Cardinal.{u}} {n : Nat} :
 lift.{v} a < n ↔ a < n
-/
theorem lift_lt_ofNat_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    lift.{v} a < ofNat(n) ↔ a < OfNat.ofNat n :=
  lift_lt_nat_iff

@[simp]
/-
**Cardinal.nat_lt_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nat_lt_lift_iff {n : Nat} {a : Cardinal.{u}} : n < lift.{v} a ↔ n < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nat_lt_lift_iff {n : ℕ} {a : Cardinal.{u}} : n < lift.{v} a ↔ n < a := by
  rw [← lift_natCast.{v, u}, lift_lt]

@[simp]
/-
**Cardinal.zero_lt_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：zero_lt_lift_iff {a : Cardinal.{u}} : (0 : Cardinal) < lift.{v} a ↔ 0 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Cardinal.nat_lt_lift_iff`：nat_lt_lift_iff {n : Nat} {a : Cardinal.{u}} :
 n < lift.{v} a ↔ n < a
-/
theorem zero_lt_lift_iff {a : Cardinal.{u}} :
    (0 : Cardinal) < lift.{v} a ↔ 0 < a := by
  simpa using nat_lt_lift_iff (n := 0)

@[simp]
/-
**Cardinal.one_lt_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：one_lt_lift_iff {a : Cardinal.{u}} : (1 : Cardinal) < lift.{v} a ↔ 1 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Cardinal.nat_lt_lift_iff`：nat_lt_lift_iff {n : Nat} {a : Cardinal.{u}} :
 n < lift.{v} a ↔ n < a
-/
theorem one_lt_lift_iff {a : Cardinal.{u}} :
    (1 : Cardinal) < lift.{v} a ↔ 1 < a := by
  simpa using nat_lt_lift_iff (n := 1)

@[simp]
/-
**Cardinal.ofNat_lt_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ofNat_lt_lift_iff {a : Cardinal.{u}} {n : Nat} [n.AtLeastTwo] : (ofNat(n) 
: Cardinal) < lift.{v} a ↔ (OfNat.ofNat n : Cardinal) < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.nat_lt_lift_iff`：nat_lt_lift_iff {n : Nat} {a : Cardinal.{u}} :
 n < lift.{v} a ↔ n < a
-/
theorem ofNat_lt_lift_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) < lift.{v} a ↔ (OfNat.ofNat n : Cardinal) < a :=
  nat_lt_lift_iff
/-
**Cardinal.mk_coe_finset** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_coe_finset {α : Type u} {s : Finset α} : #s = ↑(Finset.card s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_coe_finset {α : Type u} {s : Finset α} : #s = ↑(Finset.card s) := by simp
/-
**Cardinal.card_le_of_finset** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：card_le_of_finset {α} (s : Finset α) : (s.card : Cardinal) <= #α
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_set_le`：mk_set_le (s : Set α) : #s <= #α
· 使用定理 `Cardinal.mk_coe_finset`：mk_coe_finset {α : Type u} {s : Finset α} : #s =
 ↑(Finset.card s)
-/
theorem card_le_of_finset {α} (s : Finset α) : (s.card : Cardinal) ≤ #α :=
  @mk_coe_finset _ s ▸ mk_set_le _
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CharZero Cardinal := by
  refine ⟨fun a b h ↦ ?_⟩
  rwa [← lift_mk_fin, ← lift_mk_fin, lift_inj, Cardinal.eq, ← Fintype.card_eq,
    Fintype.card_fin, Fintype.card_fin] at h

end Cardinal

