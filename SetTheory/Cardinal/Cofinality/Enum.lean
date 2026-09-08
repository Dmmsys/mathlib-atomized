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

/-- A typeclass which expresses that the order type of a well-order equals (the initial ordinal of)
its cofinality.

If `α` is infinite, this implies that `α` is order isomorphic to `Iio c.ord` for some regular
cardinal `c`. In the informal literature, one often says that `α` is a regular cardinal, by abuse
of notation. -/
/-
**IsRegularCardinalOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [inst : LinearOrder α] → [WellFoundedLT α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass which expresses that the order type of a well-order equals (the init
ial ordinal of)
its cofinality.

If `α` is infinite, this implies that `α` is order isomorphic to `Iio c.ord` for
 some regular
cardinal `c`. In the informal literature, one often says that `α` is a regular c
ardinal, by abuse
of notation.
-/
class IsRegularCardinalOrder (α : Type*) [LinearOrder α] [WellFoundedLT α] where
  type_lt_le_ord_cof : typeLT α ≤ (cof α).ord
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsRegularCardinalOrder ℕ := ⟨by simp⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [LinearOrder α] [WellFoundedLT α] [Subsingleton α] :
    IsRegularCardinalOrder α where
  type_lt_le_ord_cof := by
    cases isEmpty_or_nonempty α
    · simpa
    · cases nonempty_unique α
      have := BoundedOrder.ofUnique α
      simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsRegularCardinalOrder Ordinal where
  type_lt_le_ord_cof := by
    rw [type_lt_ordinal, ← ord_univ, ord_le_ord, le_cof_iff]
    intro s hs
    contrapose! hs
    rw [← Cardinal.lift_id (#s), ← small_iff_lift_mk_lt_univ] at hs
    rw [not_isCofinal_iff_bddAbove]
    exact Ordinal.bddAbove_of_small

namespace Order
variable [LinearOrder α] [WellFoundedLT α] [IsRegularCardinalOrder α]

/-
**Order.ord_cof_eq_type_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：ord_cof_eq_type_lt : (cof α).ord = typeLT α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `IsRegularCardinalOrder.type_lt_le_ord_cof`：∀ {α : Type u_2} {inst : Line
arOrder α} {inst_1 : WellFoundedLT α} [self : IsRegularCardinalOrder α],   (Ordi
nal.type fun x1 x2 => x1 < x2) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.ord_le`：ord_le {c o} : ord c <= o ↔ c <= o.card
· 使用定理 `Ordinal.card_type`：card_type (r : α -> α -> Prop) [IsWellOrder α r] : ca
rd (type r) = #α
· 使用定理 `Order.cof_le_cardinalMk`：cof_le_cardinalMk : cof α <= #α
-/
theorem ord_cof_eq_type_lt : (cof α).ord = typeLT α := by
  apply IsRegularCardinalOrder.type_lt_le_ord_cof.antisymm'
  rw [ord_le, card_type]
  exact cof_le_cardinalMk α

@[simp]
/-
**Order.cof_eq_cardinalMk** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_eq_cardinalMk : cof α = #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.card_type`：card_type (r : α -> α -> Prop) [IsWellOrder α r] : ca
rd (type r) = #α
· 使用定理 `Order.ord_cof_eq_type_lt`：ord_cof_eq_type_lt : (cof α).ord = typeLT α
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
-/
theorem cof_eq_cardinalMk : cof α = #α := by
  rw [← card_type LT.lt, ← ord_cof_eq_type_lt, card_ord]

@[simp]
/-
**Order._root_.Cardinal.ord_cardinalMk** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Cardinal.ord_cardinalMk : ord #α = typeLT α := by
  rw [← ord_cof_eq_type_lt, cof_eq_cardinalMk]
/-
**Order.cof_ordinal** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_ordinal : cof Ordinal.{u} = Cardinal.univ.{u, u + 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.cof_eq_cardinalMk`：cof_eq_cardinalMk : cof α = #α
· 使用定理 `instIsRegularCardinalOrderOrdinal`：IsRegularCardinalOrder Ordinal.{u_2}
· 使用定理 `Cardinal.mk_ordinal`：mk_ordinal : #Ordinal = univ.{u, u + 1}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cof_ordinal : cof Ordinal.{u} = Cardinal.univ.{u, u + 1} := by
  simp
/-
**Order.type_eq_of_isCofinal** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：type_eq_of_isCofinal {s : Set α} (hs : IsCofinal s) : typeLT s = typeLT α
参数：hs : IsCofinal s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `RelEmbedding.ordinal_type_le`：∀ {α β : Type u_1} {r : α → α → Prop} {s :
 β → β → Prop} [inst : IsWellOrder α r] [inst_1 : IsWellOrder β s]   (h : r ↪r s
), Ordinal.type r …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.ord_cardinalMk`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1
 : WellFoundedLT α] [IsRegularCardinalOrder α],   (Cardinal.mk α).ord = Ordinal.
type fun x1 x…
· 使用定理 `Cardinal.ord_le`：ord_le {c o} : ord c <= o ↔ c <= o.card
· 使用定理 `Ordinal.card_type`：card_type (r : α -> α -> Prop) [IsWellOrder α r] : ca
rd (type r) = #α
· 使用定理 `Order.cof_eq_cardinalMk`：cof_eq_cardinalMk : cof α = #α
· 使用定理 `Order.cof_le`：cof_le {s : Set α} (h : IsCofinal s) : cof α <= #s
-/
theorem type_eq_of_isCofinal {s : Set α} (hs : IsCofinal s) : typeLT s = typeLT α := by
  apply (RelEmbedding.ofMonotone Subtype.val (by simp)).ordinal_type_le.antisymm
  rw [← ord_cardinalMk, ord_le, card_type, ← cof_eq_cardinalMk]
  exact cof_le hs

/-- Enumerate the elements of a cofinal subset of `α` by `α` itself. This is a generalization of
`Nat.nth`. -/
/-
**Order.enum** 是 Mathlib 中的一个定义，位于命名空间 `Order`。
形式化陈述：enum (s : Set α) (hs : IsCofinal s) : α ≃o s
参数：s : Set α；hs : IsCofinal s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Enumerate the elements of a cofinal subset of `α` by `α` itself. This is a gener
alization of
`Nat.nth`.
-/
noncomputable def enum (s : Set α) (hs : IsCofinal s) : α ≃o s :=
  .ofRelIsoLT (type_eq.1 (type_eq_of_isCofinal hs).symm).some

variable {s : Set α} {hs : IsCofinal s}
/-
**Order.enum_le_of_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：enum_le_of_forall_lt {a o : α} (ho : o in s) (H : forall b < a, enum s hs 
b < o) : enum s hs a <= o
参数：ho : o in s；H : forall b < a, enum s hs b < o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `OrderIso.le_symm_apply`：le_symm_apply (e : α ≃o β) {x : α} {y : β} : x <
= e.symm y ↔ e x <= y
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem enum_le_of_forall_lt {a o : α} (ho : o ∈ s) (H : ∀ b < a, enum s hs b < o) :
    enum s hs a ≤ o := by
  rw [← Subtype.coe_mk o ho, Subtype.coe_le_coe, ← OrderIso.le_symm_apply]
  apply le_of_forall_lt
  simpa [OrderIso.lt_symm_apply]
/-
**Order.enum_succ_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：enum_succ_le_of_lt [SuccOrder α] {a o : α} (ha : o in s) (H : enum s hs a 
< o) : enum s hs (succ a) <= o
参数：ha : o in s；H : enum s hs a < o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.enum_le_of_forall_lt`：enum_le_of_forall_lt {a o : α} (ho : o in s)
 (H : forall b < a, enum s hs b < o) : enum s hs a <= o
· 使用定理 `LT.lt.trans_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `Order.le_of_lt_succ`：le_of_lt_succ {a b : α} : a < succ b -> a <= b
-/
theorem enum_succ_le_of_lt [SuccOrder α] {a o : α} (ha : o ∈ s) (H : enum s hs a < o) :
    enum s hs (succ a) ≤ o := by
  refine enum_le_of_forall_lt ha fun b hb ↦ H.trans_le' ?_
  simpa using le_of_lt_succ hb

@[simp]
/-
**Order.enum_univ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：enum_univ (x : α) : enum univ .univ x = ⟨x, mem_univ x⟩
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCofinal.univ`：IsCofinal.univ : IsCofinal (@univ α)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
-/
theorem enum_univ (x : α) : enum univ .univ x = ⟨x, mem_univ x⟩ := by
  rw [← Subsingleton.allEq OrderIso.Set.univ.symm (enum univ .univ)]
  rfl
/-
**Order.enum_anti** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：enum_anti {hs : IsCofinal s} {t : Set α} {x : α} (h : s subseteq t) : enum
 t (hs.mono h) x <= (enum s hs x).1
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
· 使用定理 `IsCofinal.mono`：IsCofinal.mono {s t : Set α} (h : s subseteq t) (hs : Is
Cofinal s) : IsCofinal t
· 使用定理 `Order.enum_le_of_forall_lt`：enum_le_of_forall_lt {a o : α} (ho : o in s)
 (H : forall b < a, enum s hs b < o) : enum s hs a <= o
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
-/
theorem enum_anti {hs : IsCofinal s} {t : Set α} {x : α} (h : s ⊆ t) :
    enum t (hs.mono h) x ≤ (enum s hs x).1 := by
  induction x using WellFoundedLT.induction with | ind x IH
  exact enum_le_of_forall_lt (h (Subtype.prop _)) fun y hy ↦
    (IH y hy).trans_lt ((enum s hs).strictMono hy)

/-- A characterization of `Order.enum s _`: it is the unique strictly monotone function
with range `s`. -/
/-
**Order.enum_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：enum_eq_iff {f : α -> α} : Subtype.val ∘ enum s hs = f ↔ StrictMono f ∧ ra
nge f = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `Subtype.strictMono_coe`：Subtype.strictMono_coe [Preorder α] (p : α -> Pr
op) : StrictMono ((↑) : Subtype p -> α)
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.range_comp`：∀ {ι : Sort u_1} {ι' : Sort u_2} {E : Type u_3} [i
nst : EquivLike E ι ι'] {α : Type u_4} (f : ι' → α) (e : E),   Set.range (f ∘ ⇑e
) = Set.ra…
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StrictMono.range_inj`：StrictMono.range_inj [WellFoundedLT β] {f g : β ->
 γ} (hf : StrictMono f) (hg : StrictMono g) : Set.range f = Set.range g ↔ f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
A characterization of `Order.enum s _`: it is the unique strictly monotone funct
ion
with range `s`.
-/
theorem enum_eq_iff {f : α → α} : Subtype.val ∘ enum s hs = f ↔ StrictMono f ∧ range f = s := by
  have H := (Subtype.strictMono_coe _).comp (enum s hs).strictMono
  constructor
  · rintro rfl
    use (Subtype.strictMono_coe _).comp (enum s hs).strictMono
    simp
  · rintro ⟨hf, rfl⟩
    rw [← StrictMono.range_inj H hf]
    simp
    rfl
/-
**Order.enum_range** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：enum_range {f : α -> α} (hf : StrictMono f) : enum (range f) (isCofinal_ra
nge_of_strictMono hf) = hf.orderIso
参数：hf : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.ext`：ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g
· 使用定理 `isCofinal_range_of_strictMono`：isCofinal_range_of_strictMono [WellFounde
dLT α] {f : α -> α} (hf : StrictMono f) : IsCofinal (range f)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.enum_eq_iff`：enum_eq_iff {f : α -> α} : Subtype.val ∘ enum s hs = 
f ↔ StrictMono f ∧ range f = s
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `Subtype.strictMono_coe`：Subtype.strictMono_coe [Preorder α] (p : α -> Pr
op) : StrictMono ((↑) : Subtype p -> α)
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StrictMono.orderIso_apply`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : Preorder β] (f : α → β) (h_mono : StrictMono f)   (a : α), (
StrictMono.orde…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem enum_range {f : α → α} (hf : StrictMono f) :
    enum (range f) (isCofinal_range_of_strictMono hf) = hf.orderIso := by
  ext x
  apply congrFun (enum_eq_iff.2 ⟨?_, ?_⟩)
  · exact (Subtype.strictMono_coe _).comp (OrderIso.strictMono _)
  · simp
/-
**Order.enum_bot** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：enum_bot {α : Type*} [ConditionallyCompleteLinearOrderBot α] [WellFoundedL
T α] [IsRegularCardinalOrder α] {s : Set α} {hs : IsCofinal s} : enum s hs ⊥ = s
Inf s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_mem`：csInf_mem (hs : s.Nonempty) : sInf s in s
· 使用定理 `IsCofinal.nonempty`：IsCofinal.nonempty [Nonempty α] {s : Set α} (hs : Is
Cofinal s) : s.Nonempty
· 使用定理 `bot_nonempty`：∀ (α : Type u_1) [Bot α], Nonempty α
· 使用定理 `csInf_le'`：csInf_le' (h : a in s) : sInf s <= a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
-/
theorem enum_bot {α : Type*} [ConditionallyCompleteLinearOrderBot α] [WellFoundedLT α]
    [IsRegularCardinalOrder α] {s : Set α} {hs : IsCofinal s} : enum s hs ⊥ = sInf s := by
  let : Bot s := ⟨⟨sInf s, csInf_mem hs.nonempty⟩⟩
  let : OrderBot s := .mk fun a ↦ csInf_le' a.2
  rw [OrderIso.map_bot]
  rfl

/-- Club sets in regular cardinals correspond one to one with normal functions.

See also `Order.isNormal_enum_iff_isClub`. -/
/-
**Order.isNormal_enum_iff_dirSupClosed** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isNormal_enum_iff_dirSupClosed : IsNormal (Subtype.val ∘ enum s hs) ↔ DirS
upClosed s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `Subtype.strictMono_coe`：Subtype.strictMono_coe [Preorder α] (p : α -> Pr
op) : StrictMono ((↑) : Subtype p -> α)
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.range_comp`：∀ {ι : Sort u_1} {ι' : Sort u_2} {E : Type u_3} [i
nst : EquivLike E ι ι'] {α : Type u_4} (f : ι' → α) (e : E),   Set.range (f ∘ ⇑e
) = Set.ra…
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Order.IsNormal.dirSupClosed_range`：dirSupClosed_range {f : α -> α} (hf :
 IsNormal f) : DirSupClosed (range f)
· 使用定理 `Order.isNormal_iff`：isNormal_iff [LinearOrder α] [LinearOrder β] {f : α 
-> β} : IsNormal f ↔ StrictMono f ∧ forall o, IsSuccLimit o -> forall a, (forall
 b < o, …
· 使用定理 `dirSupClosed_iff_of_linearOrder`：dirSupClosed_iff_of_linearOrder : DirSu
pClosed s ↔ forall ⦃d⦄, d subseteq s -> d.Nonempty -> forall ⦃a⦄, IsLUB d a -> a
 in s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Order.enum_le_of_forall_lt`：enum_le_of_forall_lt {a o : α} (ho : o in s)
 (H : forall b < a, enum s hs b < o) : enum s hs a <= o
· 使用定理 `Order.IsSuccLimit.ne_bot`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → a ≠ ⊥
· 使用定理 `isLUB_csSup'`：isLUB_csSup' {s : Set α} (hs : BddAbove s) : IsLUB s (sSup
 s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.IsSuccLimit.lt_iff_exists_lt`：∀ {α : Type u_1} {a b : α} [inst : L
inearOrder α], Order.IsSuccLimit b → (a < b ↔ ∃ c < b, a < c)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `csSup_le'`：csSup_le' {s : Set α} {a : α} (h : a in upperBounds s) : sSup
 s <= a

--- 原说明 ---
Club sets in regular cardinals correspond one to one with normal functions.

See also `Order.isNormal_enum_iff_isClub`.
-/
theorem isNormal_enum_iff_dirSupClosed :
    IsNormal (Subtype.val ∘ enum s hs) ↔ DirSupClosed s := by
  let H := (Subtype.strictMono_coe _).comp (enum s hs).strictMono
  refine ⟨fun he ↦ by simpa using he.dirSupClosed_range, ?_⟩
  rw [isNormal_iff, dirSupClosed_iff_of_linearOrder]
  refine fun hs' ↦ ⟨H, fun a ha b hb ↦ ?_⟩
  have bdd : BddAbove (Subtype.val ∘ enum s hs '' Iio a) := by
    use enum s hs a
    simpa [upperBounds] using fun x hx ↦ hx.le
  have : Nonempty α := ⟨a⟩
  let := WellFoundedLT.toOrderBot α
  let := WellFoundedLT.conditionallyCompleteLinearOrderBot α
  trans sSup ((Subtype.val ∘ enum s hs) '' Iio a)
  · refine enum_le_of_forall_lt (hs' ?_ ?_ (isLUB_csSup' bdd)) fun b hb ↦ ?_
    · grind
    · simpa using ha.ne_bot
    · obtain ⟨c, hca, hbc⟩ := ha.lt_iff_exists_lt.1 hb
      refine (H hbc).trans_le <| le_csSup bdd ⟨c, ?_⟩
      simpa
  · apply csSup_le'
    simpa [upperBounds]

end Order

