/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.SetTheory.Ordinal.Basic

/-!
# Universal ordinal and cardinal

`Cardinal.univ` is the cardinality of the cardinals themselves. Likewise, `Ordinal.univ` is the
order type of the ordinals. These are related via `Cardinal.univ.ord = Ordinal.univ` and
`Ordinal.univ.card = Cardinal.univ`.

The cardinal `Cardinal.univ` is strongly inaccessible. This reflects the fact that in ZFC, the
cardinals form a proper class. See `Cardinal.IsInaccessible.univ` for a proof.

## Implementation notes

We actually define `Cardinal.univ` as the cardinality of `Ordinal`, rather than that of `Cardinal`.
This makes the basic API easier to set up. See `Cardinal.mk_cardinal` for a proof that
`Cardinal.univ = #Cardinal`.
-/

@[expose] public section

universe u v w

set_option linter.checkUnivs false in
open Ordinal in
-- intended to be used with explicit universe parameters
/-- The ordinal `univ.{u, v}` is the order type of `Ordinal.{u}` or `Cardinal.{u}`, as an element of
`Ordinal.{v}` (when `u < v`). -/
@[pp_with_univ]
/-
**Ordinal.univ** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ordinal.univ : Ordinal.{max (u + 1) v}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ordinal `univ.{u, v}` is the order type of `Ordinal.{u}` or `Cardinal.{u}`, 
as an element of
`Ordinal.{v}` (when `u < v`).
-/
def Ordinal.univ : Ordinal.{max (u + 1) v} :=
  lift.{v, u + 1} (typeLT Ordinal)

set_option linter.checkUnivs false in
open Cardinal in
-- intended to be used with explicit universe parameters
/-- The cardinal `univ.{u, v}` is the cardinality of `Ordinal.{u}` or `Cardinal.{u}`, as an element
of `Cardinal.{v}` (when `u < v`). -/
@[pp_with_univ]
/-
**Cardinal.univ** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Cardinal.univ : Cardinal.{max (u + 1) v}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cardinal `univ.{u, v}` is the cardinality of `Ordinal.{u}` or `Cardinal.{u}`
, as an element
of `Cardinal.{v}` (when `u < v`).
-/
def Cardinal.univ : Cardinal.{max (u + 1) v} :=
  lift.{v, u + 1} #Ordinal

/-! ### Universal ordinal -/

namespace Ordinal

@[simp]
/-
**Ordinal.type_lt_ordinal** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_lt_ordinal : typeLT Ordinal = univ.{u, u + 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Ordinal.lift_id`：lift_id : forall a, lift.{u, u} a = a
-/
theorem type_lt_ordinal : typeLT Ordinal = univ.{u, u + 1} :=
  (lift_id _).symm

@[deprecated type_lt_ordinal (since := "2026-03-20")]
/-
**Ordinal.univ_id** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：univ_id : univ.{u, u + 1} = typeLT Ordinal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_id`：lift_id : forall a, lift.{u, u} a = a
-/
theorem univ_id : univ.{u, u + 1} = typeLT Ordinal :=
  lift_id _

@[simp]
/-
**Ordinal.lift_univ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_lift`：lift_lift (a : Ordinal.{u}) : lift.{w} (lift.{v} a) =
 lift.{max v w} a
-/
theorem lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w} :=
  lift_lift _
/-
**Ordinal.univ_umax** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：univ_umax : univ.{u, max (u + 1) v} = univ.{u, v}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Ordinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
-/
theorem univ_umax : univ.{u, max (u + 1) v} = univ.{u, v} :=
  congr_fun lift_umax _

/-- Principal segment version of the lift operation on ordinals, embedding `Ordinal.{u}` in
`Ordinal.{v}` as a principal segment when `u < v`. -/
/-
**Ordinal.liftPrincipalSeg** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：liftPrincipalSeg : Ordinal.{u} <i Ordinal.{max (u + 1) v}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Principal segment version of the lift operation on ordinals, embedding `Ordinal.
{u}` in
`Ordinal.{v}` as a principal segment when `u < v`.
-/
def liftPrincipalSeg : Ordinal.{u} <i Ordinal.{max (u + 1) v} :=
  ⟨liftInitialSeg.{max (u + 1) v, u}, univ.{u, v}, by
    refine fun b => inductionOn b ?_; intro β s _
    rw [univ, ← lift_umax]; constructor <;> intro h
    · obtain ⟨a, e⟩ := h
      rw [← e]
      refine inductionOn a ?_
      intro α r _
      exact lift_type_lt.{u, u + 1, max (u + 1) v}.2 ⟨typein r⟩
    · rw [← lift_id (type s)] at h ⊢
      obtain ⟨f⟩ := lift_type_lt.{_,_,v}.1 h
      obtain ⟨f, a, hf⟩ := f
      exists a
      induction a using inductionOn with | type α r
      refine lift_type_eq.{u, max (u + 1) v, max (u + 1) v}.2
        ⟨(RelIso.ofSurjective (RelEmbedding.ofMonotone ?_ ?_) ?_).symm⟩
      · exact fun b => enum r ⟨f b, (hf _).1 ⟨_, rfl⟩⟩
      · refine fun a b h => (typein_lt_typein r).1 ?_
        rw [typein_enum, typein_enum]
        exact f.map_rel_iff.2 h
      · intro a'
        obtain ⟨b, e⟩ := (hf _).2 (typein_lt_type _ a')
        exists b
        simp only [RelEmbedding.ofMonotone_coe]
        simp [e]⟩

@[simp]
/-
**Ordinal.liftPrincipalSeg_coe** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：liftPrincipalSeg_coe : (liftPrincipalSeg.{u, v} : Ordinal -> Ordinal) = li
ft.{max (u + 1) v}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftPrincipalSeg_coe :
    (liftPrincipalSeg.{u, v} : Ordinal → Ordinal) = lift.{max (u + 1) v} :=
  rfl

@[simp]
/-
**Ordinal.liftPrincipalSeg_top** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：liftPrincipalSeg_top : (liftPrincipalSeg.{u, v}).top = univ.{u, v}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftPrincipalSeg_top : (liftPrincipalSeg.{u, v}).top = univ.{u, v} :=
  rfl

@[deprecated liftPrincipalSeg_top (since := "2026-03-20")]
/-
**Ordinal.liftPrincipalSeg_top'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：liftPrincipalSeg_top' : liftPrincipalSeg.{u, u + 1}.top = typeLT Ordinal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.type_lt_ordinal`：type_lt_ordinal : typeLT Ordinal = univ.{u, u +
 1}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftPrincipalSeg_top' : liftPrincipalSeg.{u, u + 1}.top = typeLT Ordinal := by
  simp

@[simp]
/-
**Ordinal.card_univ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_univ : card univ.{u, v} = Cardinal.univ.{u, v}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_univ : card univ.{u, v} = Cardinal.univ.{u, v} :=
  rfl

end Ordinal

/-! ### Universal cardinal -/

namespace Cardinal

@[simp]
/-
**Cardinal.mk_ordinal** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_ordinal : #Ordinal = univ.{u, u + 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem mk_ordinal : #Ordinal = univ.{u, u + 1} :=
  (lift_id _).symm

@[deprecated mk_ordinal (since := "2026-04-22")]
/-
**Cardinal.univ_id** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：univ_id : univ.{u, u + 1} = #Ordinal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem univ_id : univ.{u, u + 1} = #Ordinal :=
  lift_id _

@[simp]
/-
**Cardinal.lift_univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
-/
theorem lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w} :=
  lift_lift _
/-
**Cardinal.univ_umax** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：univ_umax : univ.{u, max (u + 1) v} = univ.{u, v}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
-/
theorem univ_umax : univ.{u, max (u + 1) v} = univ.{u, v} :=
  congr_fun lift_umax _
/-
**Cardinal.lift_lt_univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_lt_univ (c : Cardinal) : lift.{u + 1, u} c < univ.{u, u + 1}
参数：c : Cardinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_ord`：lift_ord (c) : Ordinal.lift.{u, v} (ord c) = ord (lif
t.{u, v} c)
· 使用定理 `Cardinal.lift_succ`：lift_succ (a) : lift.{v, u} (succ a) = succ (lift.{v
, u} a)
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `PrincipalSeg.lt_top`：lt_top (f : r ≺i s) (a : α) : s (f a) f.top
-/
theorem lift_lt_univ (c : Cardinal) : lift.{u + 1, u} c < univ.{u, u + 1} := by
  simpa only [Ordinal.liftPrincipalSeg_coe, lift_ord, lift_succ, ord_le, Order.succ_le_iff] using!
    le_of_lt (Ordinal.liftPrincipalSeg.{u, u + 1}.lt_top (Order.succ c).ord)
/-
**Cardinal.lift_lt_univ'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_lt_univ' (c : Cardinal) : lift.{max (u + 1) v, u} c < univ.{u, v}
参数：c : Cardinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Cardinal.lift_lt_univ`：lift_lt_univ (c : Cardinal) : lift.{u + 1, u} c <
 univ.{u, u + 1}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.univ_umax`：univ_umax : univ.{u, max (u + 1) v} = univ.{u, v}
· 使用定理 `Cardinal.lift_univ`：lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w}
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
-/
theorem lift_lt_univ' (c : Cardinal) : lift.{max (u + 1) v, u} c < univ.{u, v} := by
  have := lift_lt.{_, max (u + 1) v}.2 (lift_lt_univ c)
  rw [lift_lift, lift_univ, univ_umax.{u, v}] at this
  exact this

@[simp]
/-
**Cardinal.aleph0_lt_univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_lt_univ : ℵ₀ < univ.{u, v}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Cardinal.lift_lt_univ'`：lift_lt_univ' (c : Cardinal) : lift.{max (u + 1)
 v, u} c < univ.{u, v}
-/
theorem aleph0_lt_univ : ℵ₀ < univ.{u, v} := by
  simpa using lift_lt_univ' ℵ₀

@[simp]
/-
**Cardinal.nat_lt_univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nat_lt_univ (n : Nat) : n < univ.{u, v}
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
· 使用定理 `Cardinal.aleph0_lt_univ`：aleph0_lt_univ : ℵ₀ < univ.{u, v}
-/
theorem nat_lt_univ (n : ℕ) : n < univ.{u, v} := natCast_lt_aleph0.trans aleph0_lt_univ

@[simp]
/-
**Cardinal.univ_pos** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：univ_pos : 0 < univ.{u, v}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Cardinal.aleph0_lt_univ`：aleph0_lt_univ : ℵ₀ < univ.{u, v}
-/
theorem univ_pos : 0 < univ.{u, v} :=
  aleph0_lt_univ.pos

@[simp]
/-
**Cardinal.univ_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：univ_ne_zero : univ.{u, v} != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Cardinal.univ_pos`：univ_pos : 0 < univ.{u, v}
-/
theorem univ_ne_zero : univ.{u, v} ≠ 0 :=
  univ_pos.ne'

@[simp]
/-
**Cardinal.ord_univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_univ : ord univ.{u, v} = Ordinal.univ.{u, v}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Cardinal.ord_card_le`：ord_card_le (o : Ordinal) : o.card.ord <= o
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lt_ord`：lt_ord {c o} : o < ord c ↔ o.card < c
· 使用定理 `PrincipalSeg.mem_range_of_rel_top`：mem_range_of_rel_top (f : r ≺i s) {b 
: β} (h : s b f.top) : b in Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.liftPrincipalSeg_coe`：liftPrincipalSeg_coe : (liftPrincipalSeg.{
u, v} : Ordinal -> Ordinal) = lift.{max (u + 1) v}
· 使用定理 `Ordinal.lift_card`：lift_card (a) : Cardinal.lift.{u, v} (card a) = card 
(lift.{u} a)
· 使用定理 `Cardinal.lift_lt_univ'`：lift_lt_univ' (c : Cardinal) : lift.{max (u + 1)
 v, u} c < univ.{u, v}
-/
theorem ord_univ : ord univ.{u, v} = Ordinal.univ.{u, v} := by
  refine le_antisymm (ord_card_le _) <| le_of_forall_lt fun o h => lt_ord.2 ?_
  have := Ordinal.liftPrincipalSeg.mem_range_of_rel_top (by simpa using h)
  rcases this with ⟨o, h'⟩
  rw [← h', Ordinal.liftPrincipalSeg_coe, ← Ordinal.lift_card]
  apply lift_lt_univ'
/-
**Cardinal.lt_univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lt_univ {c} : c < univ.{u, u + 1} ↔ exists c', c = lift.{u + 1, u} c'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.ord_lt_ord`：ord_lt_ord {c₁ c₂} : ord c₁ < ord c₂ ↔ c₁ < c₂
· 使用定理 `PrincipalSeg.mem_range_of_rel_top`：mem_range_of_rel_top (f : r ≺i s) {b 
: β} (h : s b f.top) : b in Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.ord_univ`：ord_univ : ord univ.{u, v} = Ordinal.univ.{u, v}
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.lift_card`：lift_card (a) : Cardinal.lift.{u, v} (card a) = card 
(lift.{u} a)
· 使用定理 `Ordinal.liftPrincipalSeg_coe`：liftPrincipalSeg_coe : (liftPrincipalSeg.{
u, v} : Ordinal -> Ordinal) = lift.{max (u + 1) v}
· 使用定理 `Cardinal.lift_lt_univ`：lift_lt_univ (c : Cardinal) : lift.{u + 1, u} c <
 univ.{u, u + 1}
-/
theorem lt_univ {c} : c < univ.{u, u + 1} ↔ ∃ c', c = lift.{u + 1, u} c' :=
  ⟨fun h => by
    have := ord_lt_ord.2 h
    rw [ord_univ] at this
    obtain ⟨o, e⟩ := Ordinal.liftPrincipalSeg.mem_range_of_rel_top (by simpa)
    have := card_ord c
    rw [← e, Ordinal.liftPrincipalSeg_coe, ← Ordinal.lift_card] at this
    exact ⟨_, this.symm⟩, fun ⟨_, e⟩ => e.symm ▸ lift_lt_univ _⟩
/-
**Cardinal.lt_univ'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lt_univ' {c} : c < univ.{u, v} ↔ exists c', c = lift.{max (u + 1) v, u} c'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_lift_iff`：lt_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max 
u v}} : b < lift.{v, u} a ↔ exists a' < a, lift.{v, u} a' = b
· 使用定理 `Cardinal.lt_univ`：lt_univ {c} : c < univ.{u, u + 1} ↔ exists c', c = lif
t.{u + 1, u} c'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_ordinal`：mk_ordinal : #Ordinal = univ.{u, u + 1}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Cardinal.lift_lt_univ'`：lift_lt_univ' (c : Cardinal) : lift.{max (u + 1)
 v, u} c < univ.{u, v}
-/
theorem lt_univ' {c} : c < univ.{u, v} ↔ ∃ c', c = lift.{max (u + 1) v, u} c' :=
  ⟨fun h => by
    let ⟨a, h', e⟩ := lt_lift_iff.1 h
    rw [mk_ordinal] at h'
    rcases lt_univ.{u}.1 h' with ⟨c', rfl⟩
    exact ⟨c', by simp only [e.symm, lift_lift]⟩, fun ⟨_, e⟩ => e.symm ▸ lift_lt_univ' _⟩
/-
**Cardinal.IsStrongLimit.univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsStrongLimit`
。
形式化陈述：Cardinal.univ.{u, v}.IsStrongLimit
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.univ_ne_zero`：univ_ne_zero : univ.{u, v} != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_univ'`：lt_univ' {c} : c < univ.{u, v} ↔ exists c', c = lift.
{max (u + 1) v, u} c'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_power`：lift_power (a b : Cardinal.{u}) : lift.{v} (a ^ b) 
= lift.{v} a ^ lift.{v} b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.lift_ofNat`：lift_ofNat (n : Nat) [n.AtLeastTwo] : lift.{u} (ofN
at(n) : Cardinal.{v}) = OfNat.ofNat n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsStrongLimit.univ : IsStrongLimit univ.{u, v} :=
  ⟨univ_ne_zero, fun c h ↦ let ⟨w, h⟩ := lt_univ'.1 h; lt_univ'.2 ⟨2 ^ w, by simp [h]⟩⟩
/-
**Cardinal.small_iff_lift_mk_lt_univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：small_iff_lift_mk_lt_univ {α : Type u} : Small.{v} α ↔ Cardinal.lift.{v + 
1, _} #α < univ.{v, max u (v + 1)}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lt_univ'`：lt_univ' {c} : c < univ.{u, v} ↔ exists c', c = lift.
{max (u + 1) v, u} c'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_eq`：lift_mk_eq {α : Type u} {β : Type v} : lift.{max v 
w} #α = lift.{max u w} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_out`：mk_out (c : Cardinal) : #c.out = c
-/
theorem small_iff_lift_mk_lt_univ {α : Type u} :
    Small.{v} α ↔ Cardinal.lift.{v + 1, _} #α < univ.{v, max u (v + 1)} := by
  rw [lt_univ']
  constructor
  · rintro ⟨β, e⟩
    exact ⟨#β, lift_mk_eq.{u, _, v + 1}.2 e⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨c.out, lift_mk_eq.{u, _, v + 1}.1 (hc.trans (congr rfl c.mk_out.symm))⟩⟩

end Cardinal

