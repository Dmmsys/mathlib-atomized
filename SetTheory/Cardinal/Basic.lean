/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Data.Countable.Small
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Logic.Small.Set
public import Mathlib.Logic.UnivLE
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Basic results on cardinal numbers

We provide a collection of basic results on cardinal numbers, in particular focusing on
finite/countable/small types and sets.

## Main definitions

* `Cardinal.powerlt a b` or `a ^< b` is defined as the supremum of `a ^ c` for `c < b`.

## References

* <https://en.wikipedia.org/wiki/Cardinal_number>

## Tags

cardinal number, cardinal arithmetic, cardinal exponentiation, aleph,
Cantor's theorem, König's theorem, Konig's theorem
-/

@[expose] public section

assert_not_exists Field

open List (Vector)
open Function Order Set

noncomputable section

universe u v w v' w'

variable {α β : Type u}

namespace Cardinal

/-! ### Lifting cardinals to a higher universe -/

@[simp]
/-
**Cardinal.mk_preimage_down** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：mk_preimage_down {s : Set α} : #(ULift.down.{v} ⁻¹' s) = lift.{v} (#s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_uLift`：mk_uLift (α) : #(ULift.{v, u} α) = lift.{v} #α
· 使用定理 `Cardinal.eq`：∀ {α β : Type u}, Cardinal.mk α = Cardinal.mk β ↔ Nonempty 
(α ≃ β)
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用定理 `ULift.up_bijective`：up_bijective : Bijective (@up α)
· 使用引理 `Set.restrictPreimage_bijective`：restrictPreimage_bijective (hf : Bijecti
ve f) : Bijective (t.restrictPreimage f)
· 使用定理 `ULift.down_bijective`：down_bijective : Bijective (@down α)

--- 原说明 ---
### Lifting cardinals to a higher universe
-/
lemma mk_preimage_down {s : Set α} : #(ULift.down.{v} ⁻¹' s) = lift.{v} (#s) := by
  rw [← mk_uLift, Cardinal.eq]
  constructor
  let f : ULift.down ⁻¹' s → ULift s := fun x ↦ ULift.up (restrictPreimage s ULift.down x)
  have : Function.Bijective f :=
    ULift.up_bijective.comp (restrictPreimage_bijective _ (ULift.down_bijective))
  exact Equiv.ofBijective f this

-- `simp` can't figure out universe levels: normal form is `lift_mk_shrink'`.
/-
**Cardinal.lift_mk_shrink** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_mk_shrink (α : Type u) [Small.{v} α] : Cardinal.lift.{max u w} #(Shri
nk.{v} α) = Cardinal.lift.{max v w} #α
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_eq`：lift_mk_eq {α : Type u} {β : Type v} : lift.{max v 
w} #α = lift.{max u w} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem lift_mk_shrink (α : Type u) [Small.{v} α] :
    Cardinal.lift.{max u w} #(Shrink.{v} α) = Cardinal.lift.{max v w} #α :=
  lift_mk_eq.2 ⟨(equivShrink α).symm⟩

@[simp]
/-
**Cardinal.lift_mk_shrink'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_mk_shrink' (α : Type u) [Small.{v} α] : Cardinal.lift.{u} #(Shrink.{v
} α) = Cardinal.lift.{v} #α
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_mk_shrink`：lift_mk_shrink (α : Type u) [Small.{v} α] : Car
dinal.lift.{max u w} #(Shrink.{v} α) = Cardinal.lift.{max v w} #α
-/
theorem lift_mk_shrink' (α : Type u) [Small.{v} α] :
    Cardinal.lift.{u} #(Shrink.{v} α) = Cardinal.lift.{v} #α :=
  lift_mk_shrink.{u, v, 0} α

@[simp]
/-
**Cardinal.lift_mk_shrink''** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_mk_shrink'' (α : Type max u v) [Small.{v} α] : Cardinal.lift.{u} #(Sh
rink.{v} α) = #α
参数：α : Type max u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Cardinal.lift_mk_shrink`：lift_mk_shrink (α : Type u) [Small.{v} α] : Car
dinal.lift.{max u w} #(Shrink.{v} α) = Cardinal.lift.{max v w} #α
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem lift_mk_shrink'' (α : Type max u v) [Small.{v} α] :
    Cardinal.lift.{u} #(Shrink.{v} α) = #α := by
  rw [← lift_umax, lift_mk_shrink.{max u v, v, 0} α, ← lift_umax, lift_id]
/-
**Cardinal.prod_eq_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：prod_eq_of_fintype {α : Type u} [h : Fintype α] (f : α -> Cardinal.{v}) : 
prod f = Cardinal.lift.{u} (∏ i, f i)
参数：f : α -> Cardinal.{v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.induction_empty_option`：induction_empty_option {P : forall (α : 
Type u) [Fintype α], Prop} (of_equiv : forall (α β) [Fintype β] (e : α ≃ β), @P 
α (@Fintype.ofEquiv …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   (e : ι ≃ κ) (g : κ → M
), ∏ …
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Fintype.univ_pempty`：Fintype.univ_pempty : @univ PEmpty _ = ∅
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Cardinal.prod.eq_1`：∀ {ι : Type u} (f : ι → Cardinal.{u_1}), Cardinal.pr
od f = Cardinal.mk ((i : ι) → Quotient.out (f i))
· 使用定理 `Cardinal.mk_eq_one`：mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α]
 : #α = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Cardinal.mk_prod`：mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v
, u} #α * lift.{u, v} #β
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Cardinal.mk_out`：mk_out (c : Cardinal) : #c.out = c
· 使用定理 `Cardinal.lift_prod`：lift_prod {ι : Type u} (c : ι -> Cardinal.{v}) : lif
t.{w} (prod c) = prod fun i => lift.{w} (c i)
· 使用定理 `Fintype.prod_option`：Fintype.prod_option (f : Option α -> M) : ∏ i, f i 
= f none * ∏ i, f (some i)
· 使用定理 `Cardinal.lift_mul`：lift_mul (a b : Cardinal.{u}) : lift.{v} (a * b) = li
ft.{v} a * lift.{v} b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_eq_of_fintype {α : Type u} [h : Fintype α] (f : α → Cardinal.{v}) :
    prod f = Cardinal.lift.{u} (∏ i, f i) := by
  revert f
  refine Fintype.induction_empty_option ?_ ?_ ?_ α (h_fintype := h)
  · intro α β hβ e h f
    let := Fintype.ofEquiv β e.symm
    rw [← e.prod_comp f, ← h]
    exact mk_congr (e.piCongrLeft _).symm
  · intro f
    rw [Fintype.univ_pempty, Finset.prod_empty, lift_one, Cardinal.prod, mk_eq_one]
  · intro α hα h f
    rw [Cardinal.prod, mk_congr Equiv.piOptionEquivProd, mk_prod, lift_umax.{v, u}, mk_out, ←
        Cardinal.prod, lift_prod, Fintype.prod_option, lift_mul, ← h fun a => f (some a)]
    simp only [lift_id]

/-! ### Basic cardinals -/

/-
**Cardinal.le_one_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：le_one_iff_subsingleton {α : Type u} : #α <= 1 ↔ Subsingleton α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonULift`：∀ {α : Type u_1} [Subsingleton α], Subsingleton (
ULift.{u_2, u_1} α)
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
### Basic cardinals
-/
theorem le_one_iff_subsingleton {α : Type u} : #α ≤ 1 ↔ Subsingleton α :=
  ⟨fun ⟨f⟩ => ⟨fun _ _ => f.injective (Subsingleton.elim _ _)⟩, fun ⟨h⟩ =>
    ⟨fun _ => ULift.up 0, fun _ _ _ => h _ _⟩⟩

@[simp]
/-
**Cardinal.mk_le_one_iff_set_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_le_one_iff_set_subsingleton {s : Set α} : #s <= 1 ↔ s.Subsingleton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Cardinal.le_one_iff_subsingleton`：le_one_iff_subsingleton {α : Type u} :
 #α <= 1 ↔ Subsingleton α
· 使用定理 `Set.subsingleton_coe`：subsingleton_coe (s : Set α) : Subsingleton s ↔ s.
Subsingleton
-/
theorem mk_le_one_iff_set_subsingleton {s : Set α} : #s ≤ 1 ↔ s.Subsingleton :=
  le_one_iff_subsingleton.trans s.subsingleton_coe

alias ⟨_, _root_.Set.Subsingleton.cardinalMk_le_one⟩ := mk_le_one_iff_set_subsingleton

/-! ### Order properties -/

/-
**Cardinal.one_lt_iff_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：one_lt_iff_nontrivial {α : Type u} : 1 < #α ↔ Nontrivial α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Cardinal.le_one_iff_subsingleton`：le_one_iff_subsingleton {α : Type u} :
 #α <= 1 ↔ Subsingleton α
· 使用定理 `not_nontrivial_iff_subsingleton`：not_nontrivial_iff_subsingleton : ¬Nont
rivial α ↔ Subsingleton α
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
### Order properties
-/
theorem one_lt_iff_nontrivial {α : Type u} : 1 < #α ↔ Nontrivial α := by
  rw [← not_le, le_one_iff_subsingleton, ← not_nontrivial_iff_subsingleton, Classical.not_not]
/-
**Cardinal.sInf_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：sInf_eq_zero_iff {s : Set Cardinal} : sInf s = 0 ↔ s = ∅ ∨ exists a in s, 
a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `csInf_mem`：csInf_mem (hs : s.Nonempty) : sInf s in s
· 使用定理 `Cardinal.instWellFoundedLT`：WellFoundedLT Cardinal.{u}
· 使用定理 `Cardinal.sInf_empty`：sInf_empty : sInf (∅ : Set Cardinal.{u}) = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `csInf_le'`：csInf_le' (h : a in s) : sInf s <= a
-/
lemma sInf_eq_zero_iff {s : Set Cardinal} : sInf s = 0 ↔ s = ∅ ∨ ∃ a ∈ s, a = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases s.eq_empty_or_nonempty with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr ⟨sInf s, csInf_mem hne, h⟩
  · rcases h with rfl | ⟨a, ha, rfl⟩
    · exact Cardinal.sInf_empty
    · exact eq_bot_iff.2 (csInf_le' ha)
/-
**Cardinal.iInf_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：iInf_eq_zero_iff {ι : Sort*} {f : ι -> Cardinal} : (⨅ i, f i) = 0 ↔ IsEmpt
y ι ∨ exists i, f i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iInf_eq_zero_iff {ι : Sort*} {f : ι → Cardinal} :
    (⨅ i, f i) = 0 ↔ IsEmpty ι ∨ ∃ i, f i = 0 := by
  simp [iInf, sInf_eq_zero_iff]

/-- A variant of `ciSup_of_empty` but with `0` on the RHS for convenience -/
/-
**Cardinal.iSup_of_empty** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {ι : Sort u_1} (f : ι → Cardinal.{u_2}) [IsEmpty ι], iSup f = 0
参数：f : ι → Cardinal.{u_2}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥

--- 原说明 ---
A variant of `ciSup_of_empty` but with `0` on the RHS for convenience
-/
protected theorem iSup_of_empty {ι} (f : ι → Cardinal) [IsEmpty ι] : iSup f = 0 :=
  ciSup_of_empty f

@[simp]
/-
**Cardinal.lift_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_sInf (s : Set Cardinal) : lift.{u, v} (sInf s) = sInf (lift.{u, v} ''
 s)
参数：s : Set Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.sInf_empty`：sInf_empty : sInf (∅ : Set Cardinal.{u}) = 0
· 使用定理 `Cardinal.lift_zero`：lift_zero : lift 0 = 0
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_csInf`：Monotone.map_csInf {β : Type*} [ConditionallyComplet
eLattice β] {f : α -> β} (hf : Monotone f) (hs : s.Nonempty) : f (sInf s) = sInf
 (f '' s…
· 使用定理 `Cardinal.instWellFoundedLT`：WellFoundedLT Cardinal.{u}
· 使用定理 `Cardinal.lift_monotone`：lift_monotone : Monotone lift
-/
theorem lift_sInf (s : Set Cardinal) : lift.{u, v} (sInf s) = sInf (lift.{u, v} '' s) := by
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · simp
  · exact lift_monotone.map_csInf hs

@[simp]
/-
**Cardinal.lift_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_iInf {ι} (f : ι -> Cardinal) : lift.{u, v} (iInf f) = ⨅ i, lift.{u, v
} (f i)
参数：f : ι -> Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Cardinal.lift_sInf`：lift_sInf (s : Set Cardinal) : lift.{u, v} (sInf s) 
= sInf (lift.{u, v} '' s)
-/
theorem lift_iInf {ι} (f : ι → Cardinal) : lift.{u, v} (iInf f) = ⨅ i, lift.{u, v} (f i) := by
  unfold iInf
  convert! lift_sInf (range f)
  simp_rw [← comp_apply (f := lift), range_comp]

end Cardinal

/-! ### Small sets of cardinals -/

namespace Cardinal

set_option backward.isDefEq.respectTransparency false in
/-
**Cardinal.small_Iic** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：small_Iic (a : Cardinal.{u}) : Small.{u} (Iic a)
参数：a : Cardinal.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_out`：mk_out (c : Cardinal) : #c.out = c
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Cardinal.mk_set_le`：mk_set_le (s : Set α) : #s <= #α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.le_mk_iff_exists_set`：le_mk_iff_exists_set {c : Cardinal} {α : 
Type u} : c <= #α ↔ exists p : Set α, #p = c
-/
instance small_Iic (a : Cardinal.{u}) : Small.{u} (Iic a) := by
  rw [← mk_out a]
  apply @small_of_surjective (Set a.out) (Iic #a.out) _ fun x => ⟨#x, mk_set_le x⟩
  rintro ⟨x, hx⟩
  simpa using le_mk_iff_exists_set.1 hx
/-
**Cardinal.small_Iio** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：small_Iio (a : Cardinal.{u}) : Small.{u} (Iio a)
参数：a : Cardinal.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subset`：small_subset {s t : Set α} (hts : t subseteq s) [Small.{u}
 s] : Small.{u} t
· 使用定理 `Set.Iio_subset_Iic_self`：Iio_subset_Iic_self : Iio a subseteq Iic a
-/
instance small_Iio (a : Cardinal.{u}) : Small.{u} (Iio a) := small_subset Iio_subset_Iic_self
/-
**Cardinal.small_Icc** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：small_Icc (a b : Cardinal.{u}) : Small.{u} (Icc a b)
参数：a b : Cardinal.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subset`：small_subset {s t : Set α} (hts : t subseteq s) [Small.{u}
 s] : Small.{u} t
· 使用定理 `Set.Icc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc a b ⊆ Set.Iic b
-/
instance small_Icc (a b : Cardinal.{u}) : Small.{u} (Icc a b) := small_subset Icc_subset_Iic_self
/-
**Cardinal.small_Ico** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：small_Ico (a b : Cardinal.{u}) : Small.{u} (Ico a b)
参数：a b : Cardinal.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subset`：small_subset {s t : Set α} (hts : t subseteq s) [Small.{u}
 s] : Small.{u} t
· 使用定理 `Set.Ico_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico a b ⊆ Set.Iio b
-/
instance small_Ico (a b : Cardinal.{u}) : Small.{u} (Ico a b) := small_subset Ico_subset_Iio_self
/-
**Cardinal.small_Ioc** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：small_Ioc (a b : Cardinal.{u}) : Small.{u} (Ioc a b)
参数：a b : Cardinal.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subset`：small_subset {s t : Set α} (hts : t subseteq s) [Small.{u}
 s] : Small.{u} t
· 使用定理 `Set.Ioc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Iic b
-/
instance small_Ioc (a b : Cardinal.{u}) : Small.{u} (Ioc a b) := small_subset Ioc_subset_Iic_self
/-
**Cardinal.small_Ioo** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：small_Ioo (a b : Cardinal.{u}) : Small.{u} (Ioo a b)
参数：a b : Cardinal.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subset`：small_subset {s t : Set α} (hts : t subseteq s) [Small.{u}
 s] : Small.{u} t
· 使用定理 `Set.Ioo_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Iio b
-/
instance small_Ioo (a b : Cardinal.{u}) : Small.{u} (Ioo a b) := small_subset Ioo_subset_Iio_self

/-- A set of cardinals is bounded above iff it's small, i.e. it corresponds to a usual ZFC set. -/
/-
**Cardinal.bddAbove_iff_small** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：bddAbove_iff_small {s : Set Cardinal.{u}} : BddAbove s ↔ Small.{u} s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subset`：small_subset {s t : Set α} (hts : t subseteq s) [Small.{u}
 s] : Small.{u} t
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Cardinal.le_sum`：le_sum {ι : Type u} (f : ι -> Cardinal.{max u v}) (i) :
 f i <= sum f

--- 原说明 ---
A set of cardinals is bounded above iff it's small, i.e. it corresponds to a usu
al ZFC set.
-/
theorem bddAbove_iff_small {s : Set Cardinal.{u}} : BddAbove s ↔ Small.{u} s :=
  ⟨fun ⟨a, ha⟩ => @small_subset _ (Iic a) s (fun _ h => ha h) _, by
    rintro ⟨ι, ⟨e⟩⟩
    use sum.{u, u} fun x ↦ e.symm x
    intro a ha
    simpa using le_sum (fun x ↦ e.symm x) (e ⟨a, ha⟩)⟩
/-
**Cardinal.bddAbove_of_small** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：bddAbove_of_small {s : Set Cardinal.{u}} [h : Small.{u} s] : BddAbove s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.bddAbove_iff_small`：bddAbove_iff_small {s : Set Cardinal.{u}} :
 BddAbove s ↔ Small.{u} s
-/
theorem bddAbove_of_small {s : Set Cardinal.{u}} [h : Small.{u} s] : BddAbove s :=
  bddAbove_iff_small.2 h

@[deprecated bddAbove_of_small (since := "2026-04-04")]
/-
**Cardinal.bddAbove_range** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：bddAbove_range {ι : Type*} [Small.{u} ι] (f : ι -> Cardinal.{u}) : BddAbov
e (Set.range f)
参数：f : ι -> Cardinal.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
-/
theorem bddAbove_range {ι : Type*} [Small.{u} ι] (f : ι → Cardinal.{u}) : BddAbove (Set.range f) :=
  bddAbove_of_small
/-
**Cardinal.bddAbove_image** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：bddAbove_image (f : Cardinal.{u} -> Cardinal.{max u v}) {s : Set Cardinal.
{u}} (hs : BddAbove s) : BddAbove (f '' s)
参数：f : Cardinal.{u} -> Cardinal.{max u v}；hs : BddAbove s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.bddAbove_iff_small`：bddAbove_iff_small {s : Set Cardinal.{u}} :
 BddAbove s ↔ Small.{u} s
· 使用定理 `small_lift`：small_lift (α : Type u) [hα : Small.{v} α] : Small.{max v w}
 α
-/
theorem bddAbove_image (f : Cardinal.{u} → Cardinal.{max u v}) {s : Set Cardinal.{u}}
    (hs : BddAbove s) : BddAbove (f '' s) := by
  rw [bddAbove_iff_small] at hs ⊢
  exact small_lift _
/-
**Cardinal.bddAbove_range_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：bddAbove_range_comp {ι : Type u} {f : ι -> Cardinal.{v}} (hf : BddAbove (r
ange f)) (g : Cardinal.{v} -> Cardinal.{max v w}) : BddAbove (range (g ∘ f))
参数：hf : BddAbove (range f)；g : Cardinal.{v} -> Cardinal.{max v w}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Cardinal.bddAbove_image`：bddAbove_image (f : Cardinal.{u} -> Cardinal.{m
ax u v}) {s : Set Cardinal.{u}} (hs : BddAbove s) : BddAbove (f '' s)
-/
theorem bddAbove_range_comp {ι : Type u} {f : ι → Cardinal.{v}} (hf : BddAbove (range f))
    (g : Cardinal.{v} → Cardinal.{max v w}) : BddAbove (range (g ∘ f)) := by
  rw [range_comp]
  exact bddAbove_image g hf

/-- The type of cardinals in universe `u` is not `Small.{u}`. This is a version of the Burali-Forti
paradox. -/
/-
**Cardinal._root_.not_small_cardinal** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of cardinals in universe `u` is not `Small.{u}`. This is a version of t
he Burali-Forti
paradox.
-/
theorem _root_.not_small_cardinal : ¬ Small.{u} Cardinal.{max u v} := by
  intro h
  have := small_lift.{_, v} Cardinal.{max u v}
  rw [← small_univ_iff, ← bddAbove_iff_small] at this
  exact not_bddAbove_univ this
/-
**Cardinal.uncountable** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：uncountable : Uncountable Cardinal.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Uncountable.of_not_small`：Uncountable.of_not_small {α : Type v} (h : ¬ S
mall.{w} α) : Uncountable α
· 使用定理 `not_small_cardinal`：¬Small.{u, max (u + 1) (v + 1)} Cardinal.{max u v}
-/
instance uncountable : Uncountable Cardinal.{u} :=
  Uncountable.of_not_small not_small_cardinal.{u}

/-! ### Bounds on suprema -/

/-
**Cardinal.sum_le_lift_mk_mul_iSup_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sum_le_lift_mk_mul_iSup_lift {ι : Type u} (f : ι -> Cardinal.{v}) : sum f 
<= lift #ι * ⨆ i, lift (f i)
参数：f : ι -> Cardinal.{v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.lift_sum`：lift_sum {ι : Type u} (f : ι -> Cardinal.{v}) : Cardi
nal.lift.{w} (Cardinal.sum f) = Cardinal.sum fun i => Cardinal.lift.{w} (f i)
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Cardinal.sum_const`：sum_const (ι : Type u) (a : Cardinal.{v}) : (sum fun
 _ : ι => a) = lift.{v} #ι * lift.{u} a
· 使用定理 `Cardinal.sum_le_sum`：sum_le_sum {ι} (f g : ι -> Cardinal) (H : forall i,
 f i <= g i) : sum f <= sum g
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
### Bounds on suprema
-/
theorem sum_le_lift_mk_mul_iSup_lift {ι : Type u} (f : ι → Cardinal.{v}) :
    sum f ≤ lift #ι * ⨆ i, lift (f i) := by
  rw [← (sum f).lift_id, lift_sum, ← lift_umax.{u, v}, ← (⨆ i, lift (f i)).lift_id,
    lift_umax.{max v u, u}, ← sum_const]
  refine sum_le_sum _ _ fun i => ?_
  rw [lift_umax.{v, u}]
  exact le_ciSup bddAbove_of_small i
/-
**Cardinal.sum_le_lift_mk_mul_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sum_le_lift_mk_mul_iSup {ι : Type u} (f : ι -> Cardinal.{max u v}) : sum f
 <= lift #ι * ⨆ i, f i
参数：f : ι -> Cardinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.sum_le_lift_mk_mul_iSup_lift`：sum_le_lift_mk_mul_iSup_lift {ι :
 Type u} (f : ι -> Cardinal.{v}) : sum f <= lift #ι * ⨆ i, lift (f i)
-/
theorem sum_le_lift_mk_mul_iSup {ι : Type u} (f : ι → Cardinal.{max u v}) :
    sum f ≤ lift #ι * ⨆ i, f i := by
  simpa [← lift_umax] using sum_le_lift_mk_mul_iSup_lift f
/-
**Cardinal.sum_le_mk_mul_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sum_le_mk_mul_iSup {ι : Type u} (f : ι -> Cardinal.{u}) : sum f <= #ι * ⨆ 
i, f i
参数：f : ι -> Cardinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.sum_le_lift_mk_mul_iSup_lift`：sum_le_lift_mk_mul_iSup_lift {ι :
 Type u} (f : ι -> Cardinal.{v}) : sum f <= lift #ι * ⨆ i, lift (f i)
-/
theorem sum_le_mk_mul_iSup {ι : Type u} (f : ι → Cardinal.{u}) : sum f ≤ #ι * ⨆ i, f i := by
  simpa using sum_le_lift_mk_mul_iSup_lift f

/-- The lift of a supremum is the supremum of the lifts. -/
/-
**Cardinal.lift_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_sSup {s : Set Cardinal} (hs : BddAbove s) : lift.{u} (sSup s) = sSup 
(lift.{u} '' s)
参数：hs : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_csSup_iff'`：le_csSup_iff' {s : Set α} {a : α} (h : BddAbove s) : a <=
 sSup s ↔ forall b, b in upperBounds s -> a <= b
· 使用定理 `Cardinal.bddAbove_image`：bddAbove_image (f : Cardinal.{u} -> Cardinal.{m
ax u v}) {s : Set Cardinal.{u}} (hs : BddAbove s) : BddAbove (f '' s)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Cardinal.mem_range_lift_of_le`：mem_range_lift_of_le {a : Cardinal.{u}} {
b : Cardinal.{max u v}} : b <= lift.{v, u} a -> b in Set.range lift.{v, u}
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `csSup_le_iff'`：csSup_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : sSu
p s <= a ↔ forall x in s, x <= a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `csSup_le'`：csSup_le' {s : Set α} {a : α} (h : a in upperBounds s) : sSup
 s <= a
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s

--- 原说明 ---
The lift of a supremum is the supremum of the lifts.
-/
theorem lift_sSup {s : Set Cardinal} (hs : BddAbove s) :
    lift.{u} (sSup s) = sSup (lift.{u} '' s) := by
  apply ((le_csSup_iff' (bddAbove_image.{_, u} _ hs)).2 fun c hc => _).antisymm (csSup_le' _)
  · intro c hc
    by_contra h
    obtain ⟨d, rfl⟩ := Cardinal.mem_range_lift_of_le (not_le.1 h).le
    simp_rw [lift_le] at h hc
    rw [csSup_le_iff' hs] at h
    exact h fun a ha => lift_le.1 <| hc (mem_image_of_mem _ ha)
  · rintro i ⟨j, hj, rfl⟩
    exact lift_le.2 (le_csSup hs hj)

/-- The lift of a supremum is the supremum of the lifts. -/
/-
**Cardinal.lift_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf : BddAbove (range f)) :
 lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
参数：hf : BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Cardinal.lift_sSup`：lift_sSup {s : Set Cardinal} (hs : BddAbove s) : lif
t.{u} (sSup s) = sSup (lift.{u} '' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The lift of a supremum is the supremum of the lifts.
-/
theorem lift_iSup {ι : Type v} {f : ι → Cardinal.{w}} (hf : BddAbove (range f)) :
    lift.{u} (iSup f) = ⨆ i, lift.{u} (f i) := by
  rw [iSup, iSup, lift_sSup hf, ← range_comp]
  simp [Function.comp_def]

/-- To prove that the lift of a supremum is bounded by some cardinal `t`,
it suffices to show that the lift of each cardinal is bounded by `t`. -/
/-
**Cardinal.lift_iSup_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_iSup_le {ι : Type v} {f : ι -> Cardinal.{w}} {t : Cardinal} (hf : Bdd
Above (range f)) (w : forall i, lift.{u} (f i) <= t) : lift.{u} (iSup f) <= t
参数：hf : BddAbove (range f)；w : forall i, lift.{u} (f i) <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_iSup`：lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf :
 BddAbove (range f)) : lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a

--- 原说明 ---
To prove that the lift of a supremum is bounded by some cardinal `t`,
it suffices to show that the lift of each cardinal is bounded by `t`.
-/
theorem lift_iSup_le {ι : Type v} {f : ι → Cardinal.{w}} {t : Cardinal} (hf : BddAbove (range f))
    (w : ∀ i, lift.{u} (f i) ≤ t) : lift.{u} (iSup f) ≤ t := by
  rw [lift_iSup hf]
  exact ciSup_le' w

@[simp]
/-
**Cardinal.lift_iSup_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_iSup_le_iff {ι : Type v} {f : ι -> Cardinal.{w}} (hf : BddAbove (rang
e f)) {t : Cardinal} : lift.{u} (iSup f) <= t ↔ forall i, lift.{u} (f i) <= t
参数：hf : BddAbove (range f)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_iSup`：lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf :
 BddAbove (range f)) : lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
· 使用定理 `ciSup_le_iff'`：ciSup_le_iff' {f : ι -> α} (h : BddAbove (range f)) {a : 
α} : ⨆ i, f i <= a ↔ forall i, f i <= a
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Cardinal.bddAbove_range_comp`：bddAbove_range_comp {ι : Type u} {f : ι ->
 Cardinal.{v}} (hf : BddAbove (range f)) (g : Cardinal.{v} -> Cardinal.{max v w}
) : BddAbove (rang…
-/
theorem lift_iSup_le_iff {ι : Type v} {f : ι → Cardinal.{w}} (hf : BddAbove (range f))
    {t : Cardinal} : lift.{u} (iSup f) ≤ t ↔ ∀ i, lift.{u} (f i) ≤ t := by
  rw [lift_iSup hf]
  exact ciSup_le_iff' (bddAbove_range_comp.{_, _, u} hf _)

/-- To prove an inequality between the lifts to a common universe of two different supremums,
it suffices to show that the lift of each cardinal from the smaller supremum
if bounded by the lift of some cardinal from the larger supremum.
-/
/-
**Cardinal.lift_iSup_le_lift_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_iSup_le_lift_iSup {ι : Type v} {ι' : Type v'} {f : ι -> Cardinal.{w}}
 {f' : ι' -> Cardinal.{w'}} (hf : BddAbove (range f)) (hf' : BddAbove (range f')
) {g : ι -> ι'} (h : forall i, lift.{w'} (f i) <= lift.{w} (f' (g i))) : lift.{w
'} (iSup f) <= lift.{w} (iSup f')
参数：hf : BddAbove (range f)；hf' : BddAbove (range f')；h : forall i, lift.{w'} (f 
i) <= lift.{w} (f' (g i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_iSup`：lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf :
 BddAbove (range f)) : lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
· 使用定理 `ciSup_mono_of_forall_exists'`：ciSup_mono_of_forall_exists' {ι'} {f : ι -
> α} {g : ι' -> α} (hg : BddAbove <| range g) (h : forall i, exists i', f i <= g
 i') : ⨆ i, f i <=…
· 使用定理 `Cardinal.bddAbove_range_comp`：bddAbove_range_comp {ι : Type u} {f : ι ->
 Cardinal.{v}} (hf : BddAbove (range f)) (g : Cardinal.{v} -> Cardinal.{max v w}
) : BddAbove (rang…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
To prove an inequality between the lifts to a common universe of two different s
upremums,
it suffices to show that the lift of each cardinal from the smaller supremum
if bounded by the lift of some cardinal from the larger supremum.
-/
theorem lift_iSup_le_lift_iSup {ι : Type v} {ι' : Type v'} {f : ι → Cardinal.{w}}
    {f' : ι' → Cardinal.{w'}} (hf : BddAbove (range f)) (hf' : BddAbove (range f')) {g : ι → ι'}
    (h : ∀ i, lift.{w'} (f i) ≤ lift.{w} (f' (g i))) : lift.{w'} (iSup f) ≤ lift.{w} (iSup f') := by
  rw [lift_iSup hf, lift_iSup hf']
  exact ciSup_mono_of_forall_exists' (bddAbove_range_comp.{_, _, w} hf' _) fun i => ⟨_, h i⟩

/-- A variant of `lift_iSup_le_lift_iSup` with universes specialized via `w = v` and `w' = v'`.
This is sometimes necessary to avoid universe unification issues. -/
/-
**Cardinal.lift_iSup_le_lift_iSup'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_iSup_le_lift_iSup' {ι : Type v} {ι' : Type v'} {f : ι -> Cardinal.{v}
} {f' : ι' -> Cardinal.{v'}} (hf : BddAbove (range f)) (hf' : BddAbove (range f'
)) (g : ι -> ι') (h : forall i, lift.{v'} (f i) <= lift.{v} (f' (g i))) : lift.{
v'} (iSup f) <= lift.{v} (iSup f')
参数：hf : BddAbove (range f)；hf' : BddAbove (range f')；g : ι -> ι'；h : forall i, l
ift.{v'} (f i) <= lift.{v} (f' (g i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_iSup_le_lift_iSup`：lift_iSup_le_lift_iSup {ι : Type v} {ι'
 : Type v'} {f : ι -> Cardinal.{w}} {f' : ι' -> Cardinal.{w'}} (hf : BddAbove (r
ange f)) (hf' : BddAb…

--- 原说明 ---
A variant of `lift_iSup_le_lift_iSup` with universes specialized via `w = v` and
 `w' = v'`.
This is sometimes necessary to avoid universe unification issues.
-/
theorem lift_iSup_le_lift_iSup' {ι : Type v} {ι' : Type v'} {f : ι → Cardinal.{v}}
    {f' : ι' → Cardinal.{v'}} (hf : BddAbove (range f)) (hf' : BddAbove (range f')) (g : ι → ι')
    (h : ∀ i, lift.{v'} (f i) ≤ lift.{v} (f' (g i))) : lift.{v'} (iSup f) ≤ lift.{v} (iSup f') :=
  lift_iSup_le_lift_iSup hf hf' h
/-
**Cardinal.lift_iSup_le_sum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_iSup_le_sum {ι : Type u} [Small.{v} ι] (f : ι -> Cardinal.{v}) : lift
 (⨆ i, f i) <= sum f
参数：f : ι -> Cardinal.{v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_iSup`：lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf :
 BddAbove (range f)) : lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `Cardinal.lift_le_sum`：lift_le_sum {ι : Type u} (f : ι -> Cardinal.{v}) (
i) : lift.{u, v} (f i) <= sum f
-/
theorem lift_iSup_le_sum {ι : Type u} [Small.{v} ι] (f : ι → Cardinal.{v}) :
    lift (⨆ i, f i) ≤ sum f := by
  rw [lift_iSup bddAbove_of_small]
  exact ciSup_le' fun i => lift_le_sum f i

/-! ### Properties about the cast from `ℕ` -/

/-
**Cardinal.mk_finset_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_finset_of_fintype [Fintype α] : #(Finset α) = 2 ^ Fintype.card α
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
· 使用定理 `Fintype.card_finset`：Fintype.card_finset [Fintype α] : Fintype.card (Fin
set α) = 2 ^ Fintype.card α
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Properties about the cast from `ℕ`
-/
theorem mk_finset_of_fintype [Fintype α] : #(Finset α) = 2 ^ Fintype.card α := by
  simp

@[simp, norm_cast]
/-
**Cardinal.succ_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：succ_natCast (n : Nat) : Order.succ (n : Cardinal) = n + 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Cardinal.add_one_le_of_lt`：add_one_le_of_lt {a b : Cardinal} (h : a < b)
 : a + 1 <= b
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
-/
lemma succ_natCast (n : ℕ) : Order.succ (n : Cardinal) = n + 1 := by
  refine (succ_le_of_lt ?_).antisymm (add_one_le_of_lt <| lt_succ _)
  rw [← Nat.cast_succ]
  exact Nat.cast_lt.2 (Nat.lt_succ_self _)

@[deprecated succ_natCast (since := "2026-03-21")]
/-
**Cardinal.nat_succ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nat_succ (n : Nat) : (n.succ : Cardinal) = succ ↑n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Cardinal.succ_natCast`：succ_natCast (n : Nat) : Order.succ (n : Cardinal
) = n + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nat_succ (n : ℕ) : (n.succ : Cardinal) = succ ↑n := by
  simp

@[simp]
/-
**Cardinal.natCast_add_one_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：natCast_add_one_le_iff {n : Nat} {c : Cardinal} : n + 1 <= c ↔ n < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用引理 `Cardinal.succ_natCast`：succ_natCast (n : Nat) : Order.succ (n : Cardinal
) = n + 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma natCast_add_one_le_iff {n : ℕ} {c : Cardinal} : n + 1 ≤ c ↔ n < c := by
  rw [← Order.succ_le_iff, succ_natCast]

@[simp]
/-
**Cardinal.lt_natCast_add_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：lt_natCast_add_one_iff {n : Nat} {c : Cardinal} : c < n + 1 ↔ c <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用引理 `Cardinal.succ_natCast`：succ_natCast (n : Nat) : Order.succ (n : Cardinal
) = n + 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lt_natCast_add_one_iff {n : ℕ} {c : Cardinal} : c < n + 1 ↔ c ≤ n := by
  rw [← Order.lt_succ_iff, succ_natCast]
/-
**Cardinal.two_le_iff_one_lt** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：two_le_iff_one_lt {c : Cardinal} : 2 <= c ↔ 1 < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用引理 `Cardinal.natCast_add_one_le_iff`：natCast_add_one_le_iff {n : Nat} {c : C
ardinal} : n + 1 <= c ↔ n < c
-/
lemma two_le_iff_one_lt {c : Cardinal} : 2 ≤ c ↔ 1 < c := by
  convert! natCast_add_one_le_iff
  norm_cast

@[simp]
/-
**Cardinal.succ_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：succ_zero : succ (0 : Cardinal) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Cardinal.succ_natCast`：succ_natCast (n : Nat) : Order.succ (n : Cardinal
) = n + 1
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem succ_zero : succ (0 : Cardinal) = 1 := by norm_cast

-- This works generally to prove inequalities between numeric cardinals.
/-
**Cardinal.one_lt_two** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：one_lt_two : (1 : Cardinal) < 2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem one_lt_two : (1 : Cardinal) < 2 := by norm_cast
/-
**Cardinal.exists_finset_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：exists_finset_eq_card {α} {n : Nat} (h : n <= #α) : exists s : Finset α, n
 = s.card
参数：h : n <= #α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用引理 `Finset.exists_subset_card_eq`：exists_subset_card_eq (hns : n <= #s) : ex
ists t subseteq s, #t = n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Infinite.exists_subset_card_eq`：exists_subset_card_eq (α : Type*) [Infin
ite α] (n : Nat) : exists s : Finset α, #s = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_finset_eq_card {α} {n : ℕ} (h : n ≤ #α) :
    ∃ s : Finset α, n = s.card := by
  obtain hα | hα := finite_or_infinite α
  · let hα := Fintype.ofFinite α
    obtain ⟨t, -, rfl⟩ := @Finset.exists_subset_card_eq α .univ n <| by simpa using h
    exact ⟨t, rfl⟩
  · obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α n
    exact ⟨s, hs.symm⟩
/-
**Cardinal.exists_finset_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：exists_finset_le_card (α : Type*) (n : Nat) (h : n <= #α) : exists s : Fin
set α, n <= s.card
参数：α : Type*；n : Nat；h : n <= #α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.exists_finset_eq_card`：exists_finset_eq_card {α} {n : Nat} (h :
 n <= #α) : exists s : Finset α, n = s.card
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem exists_finset_le_card (α : Type*) (n : ℕ) (h : n ≤ #α) :
    ∃ s : Finset α, n ≤ s.card :=
  have ⟨s, eq⟩ := exists_finset_eq_card h
  ⟨s, eq.le⟩
/-
**Cardinal.card_le_of** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：card_le_of {α : Type u} {n : Nat} (H : forall s : Finset α, s.card <= n) :
 #α <= n
参数：H : forall s : Finset α, s.card <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.exists_finset_le_card`：exists_finset_le_card (α : Type*) (n : N
at) (h : n <= #α) : exists s : Finset α, n <= s.card
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem card_le_of {α : Type u} {n : ℕ} (H : ∀ s : Finset α, s.card ≤ n) : #α ≤ n := by
  contrapose! H
  apply exists_finset_le_card α (n + 1)
  simpa using H
/-
**Cardinal.cantor'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：cantor' (a) {b : Cardinal} (hb : 1 < b) : a < b ^ a
参数：a；hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Cardinal.cantor`：cantor (a : Cardinal.{u}) : a < 2 ^ a
· 使用定理 `Cardinal.power_le_power_right`：power_le_power_right {a b c : Cardinal} :
 a <= b -> a ^ c <= b ^ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Cardinal.succ_natCast`：succ_natCast (n : Nat) : Order.succ (n : Cardinal
) = n + 1
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
-/
theorem cantor' (a) {b : Cardinal} (hb : 1 < b) : a < b ^ a := by
  rw [← succ_le_iff, (by norm_cast : succ (1 : Cardinal) = 2)] at hb
  exact (cantor a).trans_le (power_le_power_right hb)
/-
**Cardinal.one_le_iff_pos** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u_1}}, 1 ≤ c ↔ 0 < c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.succ_zero`：succ_zero : succ (0 : Cardinal) = 1
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem one_le_iff_pos {c : Cardinal} : 1 ≤ c ↔ 0 < c := by
  rw [← succ_zero, succ_le_iff]
/-
**Cardinal.one_le_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u_1}}, 1 ≤ c ↔ c ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.one_le_iff_pos`：∀ {c : Cardinal.{u_1}}, 1 ≤ c ↔ 0 < c
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem one_le_iff_ne_zero {c : Cardinal} : 1 ≤ c ↔ c ≠ 0 := by
  rw [Cardinal.one_le_iff_pos, pos_iff_ne_zero]

@[simp]
/-
**Cardinal.lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c < 1 ↔ c = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `Cardinal.succ_zero`：succ_zero : succ (0 : Cardinal) = 1
· 使用定理 `Order.lt_succ_bot_iff`：lt_succ_bot_iff [NoMaxOrder α] : a < succ ⊥ ↔ a =
 ⊥
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
-/
protected theorem lt_one_iff {c : Cardinal} : c < 1 ↔ c = 0 := by
  simpa using lt_succ_bot_iff (a := c)

@[deprecated (since := "2026-03-24")]
alias lt_one_iff_zero := Cardinal.lt_one_iff
/-
**Cardinal.le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c ≤ 1 ↔ c = 0 ∨ c = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `Cardinal.succ_zero`：succ_zero : succ (0 : Cardinal) = 1
· 使用定理 `Order.le_succ_bot_iff`：le_succ_bot_iff : a <= succ ⊥ ↔ a = ⊥ ∨ a = succ 
⊥
-/
protected theorem le_one_iff {c : Cardinal} : c ≤ 1 ↔ c = 0 ∨ c = 1 := by
  simpa using le_succ_bot_iff (a := c)

/-! ### Properties about `aleph0` -/

/-
**Cardinal.natCast_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {n : ℕ}, ↑n < Cardinal.aleph0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Cardinal.natCast_add_one_le_iff`：natCast_add_one_le_iff {n : Nat} {c : C
ardinal} : n + 1 <= c ↔ n < c
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `Cardinal.lift_mk_fin`：lift_mk_fin (n : Nat) : lift #(Fin n) = n
· 使用定理 `Cardinal.aleph0.eq_1`：Cardinal.aleph0 = Cardinal.lift.{u, 0} (Cardinal.m
k ℕ)
· 使用定理 `Cardinal.lift_mk_le`：lift_mk_le {α : Type v} {β : Type w} : lift.{max u 
w} #α <= lift.{max u v} #β ↔ Nonempty (α ↪ β)
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b

--- 原说明 ---
### Properties about `aleph0`
-/
@[simp] lemma natCast_lt_aleph0 {n : ℕ} : (n : Cardinal.{u}) < ℵ₀ := by
  rw [← natCast_add_one_le_iff, ← Nat.cast_add_one, ← lift_mk_fin, aleph0, lift_mk_le.{u}]
  exact ⟨⟨(↑), fun a b => Fin.ext⟩⟩

@[deprecated natCast_lt_aleph0 (since := "2026-01-21")]
/-
**Cardinal.nat_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nat_lt_aleph0 (n : Nat) : (n : Cardinal.{u}) < ℵ₀
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem nat_lt_aleph0 (n : ℕ) : (n : Cardinal.{u}) < ℵ₀ := natCast_lt_aleph0
/-
**Cardinal.natCast_le_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {n : ℕ}, ↑n ≤ Cardinal.aleph0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
@[simp] lemma natCast_le_aleph0 {n : ℕ} : (n : Cardinal.{u}) ≤ ℵ₀ := natCast_lt_aleph0.le
/-
**Cardinal.ofNat_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {n : ℕ} [inst : n.AtLeastTwo], OfNat.ofNat n < Cardinal.aleph0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
@[simp] lemma ofNat_lt_aleph0 {n : ℕ} [n.AtLeastTwo] : ofNat(n) < ℵ₀ := natCast_lt_aleph0
/-
**Cardinal.ofNat_le_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {n : ℕ} [inst : n.AtLeastTwo], OfNat.ofNat n ≤ Cardinal.aleph0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.natCast_le_aleph0`：∀ {n : ℕ}, ↑n ≤ Cardinal.aleph0
-/
@[simp] lemma ofNat_le_aleph0 {n : ℕ} [n.AtLeastTwo] : ofNat(n) ≤ ℵ₀ := natCast_le_aleph0

@[simp]
/-
**Cardinal.one_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：one_lt_aleph0 : 1 < ℵ₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem one_lt_aleph0 : 1 < ℵ₀ := by simpa using natCast_lt_aleph0 (n := 1)

@[simp]
/-
**Cardinal.one_le_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：one_le_aleph0 : 1 <= ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.one_lt_aleph0`：one_lt_aleph0 : 1 < ℵ₀
-/
theorem one_le_aleph0 : 1 ≤ ℵ₀ :=
  one_lt_aleph0.le
/-
**Cardinal.lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, c = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_lift_iff`：lt_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max 
u v}} : b < lift.{v, u} a ↔ exists a' < a, lift.{v, u} a' = b
· 使用定理 `Cardinal.le_mk_iff_exists_set`：le_mk_iff_exists_set {c : Cardinal} {α : 
Type u} : c <= #α ↔ exists p : Set α, #p = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ ∃ n : ℕ, c = n :=
  ⟨fun h => by
    rcases lt_lift_iff.1 h with ⟨c, h', rfl⟩
    rcases le_mk_iff_exists_set.1 h'.1 with ⟨S, rfl⟩
    suffices S.Finite by
      lift S to Finset ℕ using this
      simp
    contrapose! h'
    have := Infinite.to_subtype h'
    exact ⟨Infinite.natEmbedding S⟩, fun ⟨_, e⟩ => e.symm ▸ natCast_lt_aleph0⟩
/-
**Cardinal.succ_eq_of_lt_aleph0** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：succ_eq_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : Order.succ c = c + 1
参数：h : c < ℵ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Cardinal.succ_natCast`：succ_natCast (n : Nat) : Order.succ (n : Cardinal
) = n + 1
-/
lemma succ_eq_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : Order.succ c = c + 1 := by
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp h
  rw [hn, succ_natCast]
/-
**Cardinal.aleph0_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_le {c : Cardinal} : ℵ₀ <= c ↔ forall n : Nat, ↑n <= c where mp h _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.natCast_le_aleph0`：∀ {n : ℕ}, ↑n ≤ Cardinal.aleph0
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem aleph0_le {c : Cardinal} : ℵ₀ ≤ c ↔ ∀ n : ℕ, ↑n ≤ c where
  mp h _ := natCast_le_aleph0.trans h
  mpr h := le_of_not_gt fun hn => by
    rcases lt_aleph0.1 hn with ⟨n, rfl⟩
    exact (Nat.lt_succ_self _).not_ge (Nat.cast_le.1 (h (n + 1)))
/-
**Cardinal.isSuccPrelimit_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isSuccPrelimit_aleph0 : IsSuccPrelimit ℵ₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isSuccPrelimit_of_succ_lt`：isSuccPrelimit_of_succ_lt (H : forall a
 < b, succ a < b) : IsSuccPrelimit b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Cardinal.succ_natCast`：succ_natCast (n : Nat) : Order.succ (n : Cardinal
) = n + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem isSuccPrelimit_aleph0 : IsSuccPrelimit ℵ₀ :=
  isSuccPrelimit_of_succ_lt fun a ha => by
    rcases lt_aleph0.1 ha with ⟨n, rfl⟩
    rw [succ_natCast, ← Nat.cast_add_one]
    apply natCast_lt_aleph0
/-
**Cardinal.isSuccLimit_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isSuccLimit_aleph0 : IsSuccLimit ℵ₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.isSuccLimit_iff`：∀ {c : Cardinal.{u_1}}, Order.IsSuccLimit c ↔ 
c ≠ 0 ∧ Order.IsSuccPrelimit c
· 使用定理 `Cardinal.aleph0_ne_zero`：aleph0_ne_zero : ℵ₀ != 0
· 使用定理 `Cardinal.isSuccPrelimit_aleph0`：isSuccPrelimit_aleph0 : IsSuccPrelimit ℵ
₀
-/
theorem isSuccLimit_aleph0 : IsSuccLimit ℵ₀ := by
  rw [Cardinal.isSuccLimit_iff]
  exact ⟨aleph0_ne_zero, isSuccPrelimit_aleph0⟩
/-
**Cardinal.not_isSuccLimit_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ (n : ℕ), ¬Order.IsSuccLimit ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccLimit.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a : α
}, Order.IsSuccLimit a → ¬IsMin a
· 使用定理 `isMin_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α], IsM
in ⊥
· 使用定理 `Order.not_isSuccLimit_succ`：not_isSuccLimit_succ (a : α) : ¬IsSuccLimit 
(succ a)
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Cardinal.succ_natCast`：succ_natCast (n : Nat) : Order.succ (n : Cardinal
) = n + 1
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
-/
lemma not_isSuccLimit_natCast : (n : ℕ) → ¬ IsSuccLimit (n : Cardinal.{u})
  | 0, e => e.1 isMin_bot
  | Nat.succ n, h => by
    rw [Nat.cast_succ, ← succ_natCast] at h
    exact Order.not_isSuccLimit_succ _ h
/-
**Cardinal.not_isSuccLimit_of_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：not_isSuccLimit_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : ¬ IsSuccLimit c
参数：h : c < ℵ₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `Cardinal.not_isSuccLimit_natCast`：∀ (n : ℕ), ¬Order.IsSuccLimit ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem not_isSuccLimit_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : ¬ IsSuccLimit c := by
  obtain ⟨n, rfl⟩ := lt_aleph0.1 h
  exact not_isSuccLimit_natCast n
/-
**Cardinal.aleph0_le_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_le_of_isSuccLimit {c : Cardinal} (h : IsSuccLimit c) : ℵ₀ <= c
参数：h : IsSuccLimit c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Cardinal.not_isSuccLimit_of_lt_aleph0`：not_isSuccLimit_of_lt_aleph0 {c :
 Cardinal} (h : c < ℵ₀) : ¬ IsSuccLimit c
-/
theorem aleph0_le_of_isSuccLimit {c : Cardinal} (h : IsSuccLimit c) : ℵ₀ ≤ c := by
  contrapose! h
  exact not_isSuccLimit_of_lt_aleph0 h
/-
**Cardinal.isStrongLimit_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isStrongLimit_aleph0 : IsStrongLimit ℵ₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.aleph0_ne_zero`：aleph0_ne_zero : ℵ₀ != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem isStrongLimit_aleph0 : IsStrongLimit ℵ₀ := by
  refine ⟨aleph0_ne_zero, fun x hx ↦ ?_⟩
  obtain ⟨n, rfl⟩ := lt_aleph0.1 hx
  exact mod_cast natCast_lt_aleph0
/-
**Cardinal.IsStrongLimit.aleph0_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsStrongL
imit`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsStrongLimit → Cardinal.aleph0 ≤ c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.aleph0_le_of_isSuccLimit`：aleph0_le_of_isSuccLimit {c : Cardina
l} (h : IsSuccLimit c) : ℵ₀ <= c
· 使用定理 `Cardinal.IsStrongLimit.isSuccLimit`：∀ {c : Cardinal.{u_1}}, c.IsStrongLi
mit → Order.IsSuccLimit c
-/
theorem IsStrongLimit.aleph0_le {c} (H : IsStrongLimit c) : ℵ₀ ≤ c :=
  aleph0_le_of_isSuccLimit H.isSuccLimit

@[deprecated exists_eq_ciSup_of_not_isSuccLimit (since := "2026-04-13")]
/-
**Cardinal.exists_eq_natCast_of_iSup_eq** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：exists_eq_natCast_of_iSup_eq {ι : Type u} [Nonempty ι] (f : ι -> Cardinal.
{v}) (hf : BddAbove (range f)) (n : Nat) (h : ⨆ i, f i = n) : exists i, f i = n
参数：f : ι -> Cardinal.{v}；hf : BddAbove (range f)；n : Nat；h : ⨆ i, f i = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `exists_eq_ciSup_of_not_isSuccLimit`：exists_eq_ciSup_of_not_isSuccLimit (
hbdd : BddAbove (range f)) (hf : ¬ IsSuccLimit (⨆ i, f i)) : exists i, f i = ⨆ i
, f i
· 使用定理 `Cardinal.not_isSuccLimit_natCast`：∀ (n : ℕ), ¬Order.IsSuccLimit ↑n
-/
lemma exists_eq_natCast_of_iSup_eq {ι : Type u} [Nonempty ι] (f : ι → Cardinal.{v})
    (hf : BddAbove (range f)) (n : ℕ) (h : ⨆ i, f i = n) : ∃ i, f i = n := by
  rw [← h]
  exact exists_eq_ciSup_of_not_isSuccLimit hf (h ▸ not_isSuccLimit_natCast n)

@[simp]
/-
**Cardinal.range_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：range_natCast : range ((↑) : Nat -> Cardinal) = Iio ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_natCast : range ((↑) : ℕ → Cardinal) = Iio ℵ₀ :=
  ext fun x => by simp only [mem_Iio, mem_range, eq_comm, lt_aleph0]
/-
**Cardinal.mk_eq_nat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_eq_nat_iff {α : Type u} {n : Nat} : #α = n ↔ Nonempty (α ≃ Fin n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_mk_fin`：lift_mk_fin (n : Nat) : lift #(Fin n) = n
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_eq_nat_iff {α : Type u} {n : ℕ} : #α = n ↔ Nonempty (α ≃ Fin n) := by
  rw [← lift_mk_fin, ← lift_uzero #α, lift_mk_eq']
/-
**Cardinal.lt_aleph0_iff_finite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lt_aleph0_iff_finite {α : Type u} : #α < ℵ₀ ↔ Finite α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lt_aleph0_iff_finite {α : Type u} : #α < ℵ₀ ↔ Finite α := by
  simp only [lt_aleph0, mk_eq_nat_iff, finite_iff_exists_equiv_fin]
/-
**Cardinal.lt_aleph0_iff_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lt_aleph0_iff_fintype {α : Type u} : #α < ℵ₀ ↔ Nonempty (Fintype α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Cardinal.lt_aleph0_iff_finite`：lt_aleph0_iff_finite {α : Type u} : #α < 
ℵ₀ ↔ Finite α
· 使用定理 `finite_iff_nonempty_fintype`：finite_iff_nonempty_fintype (α : Type*) : F
inite α ↔ Nonempty (Fintype α)
-/
theorem lt_aleph0_iff_fintype {α : Type u} : #α < ℵ₀ ↔ Nonempty (Fintype α) :=
  lt_aleph0_iff_finite.trans (finite_iff_nonempty_fintype _)
/-
**Cardinal.lt_aleph0_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lt_aleph0_of_finite (α : Type u) [Finite α] : #α < ℵ₀
参数：α : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lt_aleph0_iff_finite`：lt_aleph0_iff_finite {α : Type u} : #α < 
ℵ₀ ↔ Finite α
-/
theorem lt_aleph0_of_finite (α : Type u) [Finite α] : #α < ℵ₀ :=
  lt_aleph0_iff_finite.2 ‹_›
/-
**Cardinal.lt_aleph0_iff_set_finite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lt_aleph0_iff_set_finite {S : Set α} : #S < ℵ₀ ↔ S.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Cardinal.lt_aleph0_iff_finite`：lt_aleph0_iff_finite {α : Type u} : #α < 
ℵ₀ ↔ Finite α
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
-/
theorem lt_aleph0_iff_set_finite {S : Set α} : #S < ℵ₀ ↔ S.Finite :=
  lt_aleph0_iff_finite.trans finite_coe_iff

alias ⟨_, _root_.Set.Finite.lt_aleph0⟩ := lt_aleph0_iff_set_finite

@[simp]
/-
**Cardinal.lt_aleph0_iff_subtype_finite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lt_aleph0_iff_subtype_finite {p : α -> Prop} : #{ x // p x } < ℵ₀ ↔ { x | 
p x }.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lt_aleph0_iff_set_finite`：lt_aleph0_iff_set_finite {S : Set α} 
: #S < ℵ₀ ↔ S.Finite
-/
theorem lt_aleph0_iff_subtype_finite {p : α → Prop} : #{ x // p x } < ℵ₀ ↔ { x | p x }.Finite :=
  lt_aleph0_iff_set_finite
/-
**Cardinal.mk_le_aleph0_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_le_aleph0_iff : #α <= ℵ₀ ↔ Countable α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `countable_iff_nonempty_embedding`：countable_iff_nonempty_embedding : Cou
ntable α ↔ Nonempty (α ↪ Nat)
· 使用定理 `Cardinal.aleph0.eq_1`：Cardinal.aleph0 = Cardinal.lift.{u, 0} (Cardinal.m
k ℕ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_le_aleph0_iff : #α ≤ ℵ₀ ↔ Countable α := by
  rw [countable_iff_nonempty_embedding, aleph0, ← lift_uzero #α, lift_mk_le']

@[simp]
/-
**Cardinal.mk_le_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_le_aleph0 [Countable α] : #α <= ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.mk_le_aleph0_iff`：mk_le_aleph0_iff : #α <= ℵ₀ ↔ Countable α
-/
theorem mk_le_aleph0 [Countable α] : #α ≤ ℵ₀ :=
  mk_le_aleph0_iff.mpr ‹_›
/-
**Cardinal.le_aleph0_iff_set_countable** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：le_aleph0_iff_set_countable {s : Set α} : #s <= ℵ₀ ↔ s.Countable
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_le_aleph0_iff`：mk_le_aleph0_iff : #α <= ℵ₀ ↔ Countable α
-/
theorem le_aleph0_iff_set_countable {s : Set α} : #s ≤ ℵ₀ ↔ s.Countable := mk_le_aleph0_iff

alias ⟨_, _root_.Set.Countable.le_aleph0⟩ := le_aleph0_iff_set_countable

@[simp]
/-
**Cardinal.le_aleph0_iff_subtype_countable** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：le_aleph0_iff_subtype_countable {p : α -> Prop} : #{ x // p x } <= ℵ₀ ↔ { 
x | p x }.Countable
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.le_aleph0_iff_set_countable`：le_aleph0_iff_set_countable {s : S
et α} : #s <= ℵ₀ ↔ s.Countable
-/
theorem le_aleph0_iff_subtype_countable {p : α → Prop} :
    #{ x // p x } ≤ ℵ₀ ↔ { x | p x }.Countable :=
  le_aleph0_iff_set_countable
/-
**Cardinal.aleph0_lt_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_lt_mk_iff : ℵ₀ < #α ↔ Uncountable α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `not_countable_iff`：not_countable_iff : ¬Countable α ↔ Uncountable α
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Cardinal.mk_le_aleph0_iff`：mk_le_aleph0_iff : #α <= ℵ₀ ↔ Countable α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem aleph0_lt_mk_iff : ℵ₀ < #α ↔ Uncountable α := by
  rw [← not_le, ← not_countable_iff, not_iff_not, mk_le_aleph0_iff]

@[simp]
/-
**Cardinal.aleph0_lt_mk** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_lt_mk [Uncountable α] : ℵ₀ < #α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.aleph0_lt_mk_iff`：aleph0_lt_mk_iff : ℵ₀ < #α ↔ Uncountable α
-/
theorem aleph0_lt_mk [Uncountable α] : ℵ₀ < #α :=
  aleph0_lt_mk_iff.mpr ‹_›
/-
**Cardinal.canLiftCardinalNat** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：canLiftCardinalNat : CanLift Cardinal Nat (↑) fun x => x < ℵ₀
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance canLiftCardinalNat : CanLift Cardinal ℕ (↑) fun x => x < ℵ₀ :=
  ⟨fun _ hx =>
    let ⟨n, hn⟩ := lt_aleph0.mp hx
    ⟨n, hn.symm⟩⟩
/-
**Cardinal.add_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a + b < ℵ₀
参数：ha : a < ℵ₀；hb : b < ℵ₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem add_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a + b < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← Nat.cast_add]; apply natCast_lt_aleph0
/-
**Cardinal.add_lt_aleph0_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_lt_aleph0_iff {a b : Cardinal} : a + b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `self_le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] (a b : α), a ≤ a + b
· 使用定理 `self_le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canonic
allyOrderedAdd α] (a b : α), a ≤ b + a
· 使用定理 `Cardinal.add_lt_aleph0`：add_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb
 : b < ℵ₀) : a + b < ℵ₀
-/
theorem add_lt_aleph0_iff {a b : Cardinal} : a + b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ :=
  ⟨fun h => ⟨(self_le_add_right _ _).trans_lt h, (self_le_add_left _ _).trans_lt h⟩,
   fun ⟨h1, h2⟩ => add_lt_aleph0 h1 h2⟩
/-
**Cardinal.aleph0_le_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_le_add_iff {a b : Cardinal} : ℵ₀ <= a + b ↔ ℵ₀ <= a ∨ ℵ₀ <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem aleph0_le_add_iff {a b : Cardinal} : ℵ₀ ≤ a + b ↔ ℵ₀ ≤ a ∨ ℵ₀ ≤ b := by
  simp only [← not_lt, add_lt_aleph0_iff, not_and_or]

/-- See also `Cardinal.nsmul_lt_aleph0_iff_of_ne_zero` if you already have `n ≠ 0`. -/
/-
**Cardinal.nsmul_lt_aleph0_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {a : Cardinal.{u_1}} {n : ℕ}, n • a < Cardinal.aleph0 ↔ n = 0 ∨ a < Card
inal.aleph0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `Cardinal.nsmul_lt_aleph0_iff_of_ne_zero` if you already have `n ≠ 0`.
-/
theorem nsmul_lt_aleph0_iff {a : Cardinal} : ∀ {n : ℕ}, n • a < ℵ₀ ↔ n = 0 ∨ a < ℵ₀
  | 0 => by simpa using aleph0_pos
  | 1 => by simp
  | n + 2 => by rw [succ_nsmul, add_lt_aleph0_iff, nsmul_lt_aleph0_iff]; simp

/-- See also `Cardinal.nsmul_lt_aleph0_iff` for a hypothesis-free version. -/
/-
**Cardinal.nsmul_lt_aleph0_iff_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nsmul_lt_aleph0_iff_of_ne_zero {n : Nat} {a : Cardinal} (h : n != 0) : n •
 a < ℵ₀ ↔ a < ℵ₀
参数：h : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Cardinal.nsmul_lt_aleph0_iff`：∀ {a : Cardinal.{u_1}} {n : ℕ}, n • a < Ca
rdinal.aleph0 ↔ n = 0 ∨ a < Cardinal.aleph0
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)

--- 原说明 ---
See also `Cardinal.nsmul_lt_aleph0_iff` for a hypothesis-free version.
-/
theorem nsmul_lt_aleph0_iff_of_ne_zero {n : ℕ} {a : Cardinal} (h : n ≠ 0) : n • a < ℵ₀ ↔ a < ℵ₀ :=
  nsmul_lt_aleph0_iff.trans <| or_iff_right h
/-
**Cardinal.mul_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a * b < ℵ₀
参数：ha : a < ℵ₀；hb : b < ℵ₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem mul_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a * b < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← Nat.cast_mul]; apply natCast_lt_aleph0
/-
**Cardinal.mul_lt_aleph0_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_lt_aleph0_iff {a b : Cardinal} : a * b < ℵ₀ ↔ a = 0 ∨ b = 0 ∨ a < ℵ₀ ∧
 b < ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Cardinal.one_le_iff_ne_zero`：∀ {c : Cardinal.{u_1}}, 1 ≤ c ↔ c ≠ 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem mul_lt_aleph0_iff {a b : Cardinal} : a * b < ℵ₀ ↔ a = 0 ∨ b = 0 ∨ a < ℵ₀ ∧ b < ℵ₀ := by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases ha : a = 0
    · exact Or.inl ha
    right
    by_cases hb : b = 0
    · exact Or.inl hb
    right
    rw [← Ne, ← Cardinal.one_le_iff_ne_zero] at ha hb
    constructor
    · rw [← mul_one a]
      exact (mul_le_mul' le_rfl hb).trans_lt h
    · rw [← one_mul b]
      exact (mul_le_mul' ha le_rfl).trans_lt h
  rintro (rfl | rfl | ⟨ha, hb⟩) <;> simp only [*, mul_lt_aleph0, aleph0_pos, zero_mul, mul_zero]

/-- See also `Cardinal.aleph0_le_mul_iff`. -/
/-
**Cardinal.aleph0_le_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_le_mul_iff {a b : Cardinal} : ℵ₀ <= a * b ↔ a != 0 ∧ b != 0 ∧ (ℵ₀ <
= a ∨ ℵ₀ <= b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Cardinal.mul_lt_aleph0_iff`：mul_lt_aleph0_iff {a b : Cardinal} : a * b <
 ℵ₀ ↔ a = 0 ∨ b = 0 ∨ a < ℵ₀ ∧ b < ℵ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q

--- 原说明 ---
See also `Cardinal.aleph0_le_mul_iff`.
-/
theorem aleph0_le_mul_iff {a b : Cardinal} : ℵ₀ ≤ a * b ↔ a ≠ 0 ∧ b ≠ 0 ∧ (ℵ₀ ≤ a ∨ ℵ₀ ≤ b) := by
  let h := (@mul_lt_aleph0_iff a b).not
  rwa [not_lt, not_or, not_or, not_and_or, not_lt, not_lt] at h

/-- See also `Cardinal.aleph0_le_mul_iff'`. -/
/-
**Cardinal.aleph0_le_mul_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_le_mul_iff' {a b : Cardinal.{u}} : ℵ₀ <= a * b ↔ a != 0 ∧ ℵ₀ <= b ∨
 ℵ₀ <= a ∧ b != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥
· 使用定理 `Cardinal.aleph0_ne_zero`：aleph0_ne_zero : ℵ₀ != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `and_left_comm`：∀ {a b c : Prop}, a ∧ b ∧ c ↔ b ∧ a ∧ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
See also `Cardinal.aleph0_le_mul_iff'`.
-/
theorem aleph0_le_mul_iff' {a b : Cardinal.{u}} : ℵ₀ ≤ a * b ↔ a ≠ 0 ∧ ℵ₀ ≤ b ∨ ℵ₀ ≤ a ∧ b ≠ 0 := by
  have : ∀ {a : Cardinal.{u}}, ℵ₀ ≤ a → a ≠ 0 := fun a => ne_bot_of_le_ne_bot aleph0_ne_zero a
  simp only [aleph0_le_mul_iff, and_or_left, and_iff_right_of_imp this, @and_left_comm (a ≠ 0)]
  simp only [and_comm, or_comm]
/-
**Cardinal.mul_lt_aleph0_iff_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_lt_aleph0_iff_of_ne_zero {a b : Cardinal} (ha : a != 0) (hb : b != 0) 
: a * b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀
参数：ha : a != 0；hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mul_lt_aleph0_iff_of_ne_zero {a b : Cardinal} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ := by simp [mul_lt_aleph0_iff, ha, hb]
/-
**Cardinal.power_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a ^ b < ℵ₀
参数：ha : a < ℵ₀；hb : b < ℵ₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.power_natCast`：power_natCast (a : Cardinal.{u}) (n : Nat) : a ^
 (↑n : Cardinal.{u}) = a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem power_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a ^ b < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [power_natCast, ← Nat.cast_pow]; apply natCast_lt_aleph0
/-
**Cardinal.eq_one_iff_unique** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：eq_one_iff_unique {α : Type*} : #α = 1 ↔ Subsingleton α ∧ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Cardinal.le_one_iff_subsingleton`：le_one_iff_subsingleton {α : Type u} :
 #α <= 1 ↔ Subsingleton α
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Cardinal.one_le_iff_ne_zero`：∀ {c : Cardinal.{u_1}}, 1 ≤ c ↔ c ≠ 0
· 使用定理 `Cardinal.mk_ne_zero_iff`：mk_ne_zero_iff {α : Type u} : #α != 0 ↔ Nonempt
y α
-/
theorem eq_one_iff_unique {α : Type*} : #α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  calc
    #α = 1 ↔ #α ≤ 1 ∧ 1 ≤ #α := le_antisymm_iff
    _ ↔ Subsingleton α ∧ Nonempty α :=
      le_one_iff_subsingleton.and (Cardinal.one_le_iff_ne_zero.trans mk_ne_zero_iff)
/-
**Cardinal.infinite_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ <= #α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Cardinal.lt_aleph0_iff_finite`：lt_aleph0_iff_finite {α : Type u} : #α < 
ℵ₀ ↔ Finite α
· 使用定理 `not_finite_iff_infinite`：not_finite_iff_infinite : ¬Finite α ↔ Infinite 
α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ ≤ #α := by
  rw [← not_lt, lt_aleph0_iff_finite, not_finite_iff_infinite]
/-
**Cardinal.aleph0_le_mk_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_le_mk_iff : ℵ₀ <= #α ↔ Infinite α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Cardinal.infinite_iff`：infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ <= #α
-/
lemma aleph0_le_mk_iff : ℵ₀ ≤ #α ↔ Infinite α := infinite_iff.symm
/-
**Cardinal.mk_lt_aleph0_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：mk_lt_aleph0_iff : #α < ℵ₀ ↔ Finite α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mk_lt_aleph0_iff : #α < ℵ₀ ↔ Finite α := by simp [← not_le, aleph0_le_mk_iff]
/-
**Cardinal.mk_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {α : Type u} [Finite α], Cardinal.mk α < Cardinal.aleph0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Cardinal.mk_lt_aleph0_iff`：mk_lt_aleph0_iff : #α < ℵ₀ ↔ Finite α
-/
@[simp] lemma mk_lt_aleph0 [Finite α] : #α < ℵ₀ := mk_lt_aleph0_iff.2 ‹_›

@[simp]
/-
**Cardinal.aleph0_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.infinite_iff`：infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ <= #α
-/
theorem aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ ≤ #α :=
  infinite_iff.1 ‹_›
/-
**Cardinal._root_.Infinite.of_cardinalMk_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Infinite.of_cardinalMk_le {α β : Type u} [Infinite α] (h : #α ≤ #β) :
    Infinite β := infinite_iff.2 <| (aleph0_le_mk α).trans h

@[simp]
/-
**Cardinal.mk_eq_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_eq_aleph0 (α : Type*) [Countable α] [Infinite α] : #α = ℵ₀
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Cardinal.mk_le_aleph0`：mk_le_aleph0 [Countable α] : #α <= ℵ₀
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
-/
theorem mk_eq_aleph0 (α : Type*) [Countable α] [Infinite α] : #α = ℵ₀ :=
  mk_le_aleph0.antisymm <| aleph0_le_mk _
/-
**Cardinal.denumerable_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：denumerable_iff {α : Type u} : Nonempty (Denumerable α) ↔ #α = ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
-/
theorem denumerable_iff {α : Type u} : Nonempty (Denumerable α) ↔ #α = ℵ₀ :=
  ⟨fun ⟨h⟩ => mk_congr ((@Denumerable.eqv α h).trans Equiv.ulift.symm), fun h => by
    obtain ⟨f⟩ := Quotient.exact h
    exact ⟨Denumerable.mk' <| f.trans Equiv.ulift⟩⟩
/-
**Cardinal.mk_denumerable** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_denumerable (α : Type u) [Denumerable α] : #α = ℵ₀
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.denumerable_iff`：denumerable_iff {α : Type u} : Nonempty (Denum
erable α) ↔ #α = ℵ₀
-/
theorem mk_denumerable (α : Type u) [Denumerable α] : #α = ℵ₀ :=
  denumerable_iff.1 ⟨‹_›⟩
/-
**Cardinal._root_.Set.countable_infinite_iff_nonempty_denumerable** 是 Mathlib 中的
一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.countable_infinite_iff_nonempty_denumerable {α : Type*} {s : Set α} :
    s.Countable ∧ s.Infinite ↔ Nonempty (Denumerable s) := by
  rw [nonempty_denumerable_iff, ← Set.infinite_coe_iff, countable_coe_iff]

@[simp]
/-
**Cardinal.aleph0_add_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_add_aleph0 : ℵ₀ + ℵ₀ = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_denumerable`：mk_denumerable (α : Type u) [Denumerable α] : #
α = ℵ₀
-/
theorem aleph0_add_aleph0 : ℵ₀ + ℵ₀ = ℵ₀ :=
  mk_denumerable _
/-
**Cardinal.aleph0_mul_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_mul_aleph0 : ℵ₀ * ℵ₀ = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_denumerable`：mk_denumerable (α : Type u) [Denumerable α] : #
α = ℵ₀
-/
theorem aleph0_mul_aleph0 : ℵ₀ * ℵ₀ = ℵ₀ :=
  mk_denumerable _

@[simp]
/-
**Cardinal.nat_mul_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nat_mul_aleph0 {n : Nat} (hn : n != 0) : ↑n * ℵ₀ = ℵ₀
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Cardinal.mk_le_aleph0`：mk_le_aleph0 [Countable α] : #α <= ℵ₀
· 使用定理 `instCountableProd`：∀ {α : Type u} {β : Type v} [Countable α] [Countable 
β], Countable (α × β)
· 使用定理 `instCountableULift`：∀ {β : Type v} [Countable β], Countable (ULift.{u, v
} β)
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Cardinal.lift_mk_fin`：lift_mk_fin (n : Nat) : lift #(Fin n) = n
· 使用定理 `le_mul_of_one_le_left`：le_mul_of_one_le_left [MulPosMono α] (hb : 0 <= b
) (h : 1 <= a) : b <= a * b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
-/
theorem nat_mul_aleph0 {n : ℕ} (hn : n ≠ 0) : ↑n * ℵ₀ = ℵ₀ :=
  le_antisymm (lift_mk_fin n ▸ mk_le_aleph0) <|
    le_mul_of_one_le_left zero_le <| by rwa [← Nat.cast_one, Nat.cast_le, Nat.one_le_iff_ne_zero]

@[simp]
/-
**Cardinal.aleph0_mul_nat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_mul_nat {n : Nat} (hn : n != 0) : ℵ₀ * n = ℵ₀
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Cardinal.nat_mul_aleph0`：nat_mul_aleph0 {n : Nat} (hn : n != 0) : ↑n * ℵ
₀ = ℵ₀
-/
theorem aleph0_mul_nat {n : ℕ} (hn : n ≠ 0) : ℵ₀ * n = ℵ₀ := by rw [mul_comm, nat_mul_aleph0 hn]

@[simp]
/-
**Cardinal.ofNat_mul_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ofNat_mul_aleph0 {n : Nat} [Nat.AtLeastTwo n] : ofNat(n) * ℵ₀ = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.nat_mul_aleph0`：nat_mul_aleph0 {n : Nat} (hn : n != 0) : ↑n * ℵ
₀ = ℵ₀
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
-/
theorem ofNat_mul_aleph0 {n : ℕ} [Nat.AtLeastTwo n] : ofNat(n) * ℵ₀ = ℵ₀ :=
  nat_mul_aleph0 (NeZero.ne n)

@[simp]
/-
**Cardinal.aleph0_mul_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_mul_ofNat {n : Nat} [Nat.AtLeastTwo n] : ℵ₀ * ofNat(n) = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.aleph0_mul_nat`：aleph0_mul_nat {n : Nat} (hn : n != 0) : ℵ₀ * n
 = ℵ₀
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
-/
theorem aleph0_mul_ofNat {n : ℕ} [Nat.AtLeastTwo n] : ℵ₀ * ofNat(n) = ℵ₀ :=
  aleph0_mul_nat (NeZero.ne n)

@[simp]
/-
**Cardinal.add_le_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_le_aleph0 {c₁ c₂ : Cardinal} : c₁ + c₂ <= ℵ₀ ↔ c₁ <= ℵ₀ ∧ c₂ <= ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Cardinal.aleph0_add_aleph0`：aleph0_add_aleph0 : ℵ₀ + ℵ₀ = ℵ₀
-/
theorem add_le_aleph0 {c₁ c₂ : Cardinal} : c₁ + c₂ ≤ ℵ₀ ↔ c₁ ≤ ℵ₀ ∧ c₂ ≤ ℵ₀ :=
  ⟨fun h => ⟨le_self_add.trans h, le_add_self.trans h⟩, fun h =>
    aleph0_add_aleph0 ▸ add_le_add h.1 h.2⟩

@[simp]
/-
**Cardinal.aleph0_add_nat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_add_nat (n : Nat) : ℵ₀ + n = ℵ₀
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.add_le_aleph0`：add_le_aleph0 {c₁ c₂ : Cardinal} : c₁ + c₂ <= ℵ₀
 ↔ c₁ <= ℵ₀ ∧ c₂ <= ℵ₀
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Cardinal.natCast_le_aleph0`：∀ {n : ℕ}, ↑n ≤ Cardinal.aleph0
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
-/
theorem aleph0_add_nat (n : ℕ) : ℵ₀ + n = ℵ₀ :=
  (add_le_aleph0.2 ⟨le_rfl, natCast_le_aleph0⟩).antisymm le_self_add

@[simp]
/-
**Cardinal.nat_add_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nat_add_aleph0 (n : Nat) : ↑n + ℵ₀ = ℵ₀
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Cardinal.aleph0_add_nat`：aleph0_add_nat (n : Nat) : ℵ₀ + n = ℵ₀
-/
theorem nat_add_aleph0 (n : ℕ) : ↑n + ℵ₀ = ℵ₀ := by rw [add_comm, aleph0_add_nat]

@[simp]
/-
**Cardinal.ofNat_add_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ofNat_add_aleph0 {n : Nat} [Nat.AtLeastTwo n] : ofNat(n) + ℵ₀ = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.nat_add_aleph0`：nat_add_aleph0 (n : Nat) : ↑n + ℵ₀ = ℵ₀
-/
theorem ofNat_add_aleph0 {n : ℕ} [Nat.AtLeastTwo n] : ofNat(n) + ℵ₀ = ℵ₀ :=
  nat_add_aleph0 n

@[simp]
/-
**Cardinal.aleph0_add_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_add_ofNat {n : Nat} [Nat.AtLeastTwo n] : ℵ₀ + ofNat(n) = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.aleph0_add_nat`：aleph0_add_nat (n : Nat) : ℵ₀ + n = ℵ₀
-/
theorem aleph0_add_ofNat {n : ℕ} [Nat.AtLeastTwo n] : ℵ₀ + ofNat(n) = ℵ₀ :=
  aleph0_add_nat n
/-
**Cardinal.exists_nat_eq_of_le_nat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：exists_nat_eq_of_le_nat {c : Cardinal} {n : Nat} (h : c <= n) : exists m, 
m <= n ∧ c = m
参数：h : c <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
-/
theorem exists_nat_eq_of_le_nat {c : Cardinal} {n : ℕ} (h : c ≤ n) : ∃ m, m ≤ n ∧ c = m := by
  lift c to ℕ using h.trans_lt natCast_lt_aleph0
  exact ⟨c, mod_cast h, rfl⟩
/-
**Cardinal.mk_int** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_int : #Int = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_denumerable`：mk_denumerable (α : Type u) [Denumerable α] : #
α = ℵ₀
-/
theorem mk_int : #ℤ = ℵ₀ :=
  mk_denumerable ℤ
/-
**Cardinal.mk_pnat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_pnat : #Nat+ = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_denumerable`：mk_denumerable (α : Type u) [Denumerable α] : #
α = ℵ₀
-/
theorem mk_pnat : #ℕ+ = ℵ₀ :=
  mk_denumerable ℕ+

/-! ### Cardinalities of basic sets and types -/

/-
**Cardinal.mk_additive** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {α : Type u}, Cardinal.mk (Additive α) = Cardinal.mk α
参数：Additive α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Cardinalities of basic sets and types
-/
@[simp] theorem mk_additive : #(Additive α) = #α := rfl
/-
**Cardinal.mk_multiplicative** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {α : Type u}, Cardinal.mk (Multiplicative α) = Cardinal.mk α
参数：Multiplicative α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Cardinalities of basic sets and types
-/
@[simp] theorem mk_multiplicative : #(Multiplicative α) = #α := rfl
/-
**Cardinal.mk_mulOpposite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {α : Type u}, Cardinal.mk αᵐᵒᵖ = Cardinal.mk α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
### Cardinalities of basic sets and types
-/
@[to_additive (attr := simp)] theorem mk_mulOpposite : #(MulOpposite α) = #α :=
  mk_congr MulOpposite.opEquiv.symm
/-
**Cardinal.mk_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_singleton {α : Type u} (x : α) : #({x} : Set α) = 1
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_eq_one`：mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α]
 : #α = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem mk_singleton {α : Type u} (x : α) : #({x} : Set α) = 1 :=
  mk_eq_one _

@[simp]
/-
**Cardinal.mk_vector** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_vector (α : Type u) (n : Nat) : #(List.Vector α n) = #α ^ n
参数：α : Type u；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_pi`：mk_pi {ι : Type u} (α : ι -> Type v) : #(Π i, α i) = pro
d fun i => #(α i)
· 使用定理 `Cardinal.prod_const`：prod_const (ι : Type u) (a : Cardinal.{v}) : (prod 
fun _ : ι => a) = lift.{u} a ^ lift.{v} #ι
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_vector (α : Type u) (n : ℕ) : #(List.Vector α n) = #α ^ n :=
  (mk_congr (Equiv.vectorEquivFin α n)).trans <| by simp
/-
**Cardinal.mk_list_eq_sum_pow** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_list_eq_sum_pow (α : Type u) : #(List α) = sum fun n => #α ^ n
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.mk_vector`：mk_vector (α : Type u) (n : Nat) : #(List.Vector α n
) = #α ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_list_eq_sum_pow (α : Type u) : #(List α) = sum fun n ↦ #α ^ n :=
  calc
    #(List α) = #(Σ n, List.Vector α n) := mk_congr (Equiv.sigmaFiberEquiv List.length).symm
    _ = sum fun n ↦ #α ^ n := by simp
/-
**Cardinal.sum_zero_pow** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sum_zero_pow : sum (fun n => (0 : Cardinal) ^ n) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `Cardinal.mk_list_eq_sum_pow`：mk_list_eq_sum_pow (α : Type u) : #(List α)
 = sum fun n => #α ^ n
· 使用定理 `Cardinal.mk_eq_one`：mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α]
 : #α = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem sum_zero_pow : sum (fun n ↦ (0 : Cardinal) ^ n) = 1 := by
  rw [← mk_eq_zero (α := PEmpty), ← mk_list_eq_sum_pow, mk_eq_one]
/-
**Cardinal.mk_quot_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_quot_le {α : Type u} {r : α -> α -> Prop} : #(Quot r) <= #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_le_of_surjective`：mk_le_of_surjective {α β : Type u} {f : α 
-> β} (hf : Surjective f) : #β <= #α
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q
-/
theorem mk_quot_le {α : Type u} {r : α → α → Prop} : #(Quot r) ≤ #α :=
  mk_le_of_surjective Quot.exists_rep
/-
**Cardinal.mk_quotient_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_quotient_le {α : Type u} {s : Setoid α} : #(Quotient s) <= #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_quot_le`：mk_quot_le {α : Type u} {r : α -> α -> Prop} : #(Qu
ot r) <= #α
-/
theorem mk_quotient_le {α : Type u} {s : Setoid α} : #(Quotient s) ≤ #α :=
  mk_quot_le
/-
**Cardinal.mk_subtype_le_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_subtype_le_of_subset {α : Type u} {p q : α -> Prop} (h : forall ⦃x⦄, p 
x -> q x) : #(Subtype p) <= #(Subtype q)
参数：h : forall ⦃x⦄, p x -> q x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_subtype_le_of_subset {α : Type u} {p q : α → Prop} (h : ∀ ⦃x⦄, p x → q x) :
    #(Subtype p) ≤ #(Subtype q) :=
  ⟨Embedding.subtypeMap (Embedding.refl α) h⟩
/-
**Cardinal.mk_le_mk_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_le_mk_of_subset {α} {s t : Set α} (h : s subseteq t) : #s <= #t
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_le_mk_of_subset {α} {s t : Set α} (h : s ⊆ t) : #s ≤ #t :=
  ⟨Set.embeddingOfSubset s t h⟩
/-
**Cardinal.mk_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_monotone : Monotone (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
-/
theorem mk_monotone : Monotone (α := Set α) (mk ∘ (↑)) :=
  fun _ _ ↦ mk_le_mk_of_subset

@[deprecated mk_eq_zero (since := "2026-01-31")]
/-
**Cardinal.mk_emptyCollection** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_emptyCollection (α : Type u) : #(∅ : Set α) = 0
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
-/
theorem mk_emptyCollection (α : Type u) : #(∅ : Set α) = 0 :=
  mk_eq_zero _
/-
**Cardinal.mk_set_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_set_eq_zero_iff {s : Set α} : #s = 0 ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_eq_zero_iff`：mk_eq_zero_iff {α : Type u} : #α = 0 ↔ IsEmpty 
α
· 使用定理 `Set.isEmpty_coe_sort`：isEmpty_coe_sort {s : Set α} : IsEmpty (↥s) ↔ s = 
∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_set_eq_zero_iff {s : Set α} : #s = 0 ↔ s = ∅ := by
  rw [mk_eq_zero_iff, isEmpty_coe_sort]

@[deprecated (since := "2026-01-31")]
alias mk_emptyCollection_iff := mk_set_eq_zero_iff
/-
**Cardinal.mk_set_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_set_ne_zero_iff {s : Set α} : #s != 0 ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_ne_zero_iff`：mk_ne_zero_iff {α : Type u} : #α != 0 ↔ Nonempt
y α
· 使用定理 `Set.nonempty_coe_sort`：nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.N
onempty
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_set_ne_zero_iff {s : Set α} : #s ≠ 0 ↔ s.Nonempty := by
  rw [mk_ne_zero_iff, nonempty_coe_sort]

@[simp]
/-
**Cardinal.mk_univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_univ {α : Type u} : #(@univ α) = #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
-/
theorem mk_univ {α : Type u} : #(@univ α) = #α :=
  mk_congr (Equiv.Set.univ α)
/-
**Cardinal.mk_setProd** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {α β : Type u} (s : Set α) (t : Set β), Cardinal.mk ↑(s ×ˢ t) = Cardinal
.mk ↑s * Cardinal.mk ↑t
参数：s : Set α；t : Set β；s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mul_def`：mul_def (α β : Type u) : #α * #β = #(α × β)
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
-/
@[simp] lemma mk_setProd {α β : Type u} (s : Set α) (t : Set β) : #(s ×ˢ t) = #s * #t := by
  rw [mul_def, mk_congr (Equiv.Set.prod ..)]
/-
**Cardinal.mk_image_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_image_le {α β : Type u} {f : α -> β} {s : Set α} : #(f '' s) <= #s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_le_of_surjective`：mk_le_of_surjective {α β : Type u} {f : α 
-> β} (hf : Surjective f) : #β <= #α
· 使用定理 `Set.imageFactorization_surjective`：imageFactorization_surjective {f : α 
-> β} {s : Set α} : Surjective (imageFactorization f s)
-/
theorem mk_image_le {α β : Type u} {f : α → β} {s : Set α} : #(f '' s) ≤ #s :=
  mk_le_of_surjective imageFactorization_surjective
/-
**Cardinal.mk_image2_le** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：mk_image2_le {α β γ : Type u} {f : α -> β -> γ} {s : Set α} {t : Set β} : 
#(image2 f s t) <= #s * #t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_uncurry_prod`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} (
f : α → β → γ) (s : Set α) (t : Set β),   Function.uncurry f '' s ×ˢ t = Set.ima
ge2 f s t
· 使用定理 `Cardinal.mk_setProd`：∀ {α β : Type u} (s : Set α) (t : Set β), Cardinal.
mk ↑(s ×ˢ t) = Cardinal.mk ↑s * Cardinal.mk ↑t
· 使用定理 `Cardinal.mk_image_le`：mk_image_le {α β : Type u} {f : α -> β} {s : Set α
} : #(f '' s) <= #s
-/
lemma mk_image2_le {α β γ : Type u} {f : α → β → γ} {s : Set α} {t : Set β} :
    #(image2 f s t) ≤ #s * #t := by
  rw [← image_uncurry_prod, ← mk_setProd]
  exact mk_image_le
/-
**Cardinal.mk_image_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_image_le_lift {α : Type u} {β : Type v} {f : α -> β} {s : Set α} : lift
.{u} #(f '' s) <= lift.{v} #s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_le`：lift_mk_le {α : Type v} {β : Type w} : lift.{max u 
w} #α <= lift.{max u v} #β ↔ Nonempty (α ↪ β)
· 使用定理 `Set.imageFactorization_surjective`：imageFactorization_surjective {f : α 
-> β} {s : Set α} : Surjective (imageFactorization f s)
-/
theorem mk_image_le_lift {α : Type u} {β : Type v} {f : α → β} {s : Set α} :
    lift.{u} #(f '' s) ≤ lift.{v} #s :=
  lift_mk_le.{0}.mpr ⟨Embedding.ofSurjective _ imageFactorization_surjective⟩
/-
**Cardinal.mk_range_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_range_le {α β : Type u} {f : α -> β} : #(range f) <= #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_le_of_surjective`：mk_le_of_surjective {α β : Type u} {f : α 
-> β} (hf : Surjective f) : #β <= #α
· 使用定理 `Set.rangeFactorization_surjective`：∀ {α : Type u} {ι : Sort u_1} {f : ι 
→ α}, Function.Surjective (Set.rangeFactorization f)
-/
theorem mk_range_le {α β : Type u} {f : α → β} : #(range f) ≤ #α :=
  mk_le_of_surjective rangeFactorization_surjective
/-
**Cardinal.mk_range_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_range_le_lift {α : Type u} {β : Type v} {f : α -> β} : lift.{u} #(range
 f) <= lift.{v} #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_le`：lift_mk_le {α : Type v} {β : Type w} : lift.{max u 
w} #α <= lift.{max u v} #β ↔ Nonempty (α ↪ β)
· 使用定理 `Set.rangeFactorization_surjective`：∀ {α : Type u} {ι : Sort u_1} {f : ι 
→ α}, Function.Surjective (Set.rangeFactorization f)
-/
theorem mk_range_le_lift {α : Type u} {β : Type v} {f : α → β} :
    lift.{u} #(range f) ≤ lift.{v} #α :=
  lift_mk_le.{0}.mpr ⟨Embedding.ofSurjective _ rangeFactorization_surjective⟩
/-
**Cardinal.mk_range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_range_eq (f : α -> β) (h : Injective f) : #(range f) = #α
参数：f : α -> β；h : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mk_range_eq (f : α → β) (h : Injective f) : #(range f) = #α :=
  mk_congr (Equiv.ofInjective f h).symm
/-
**Cardinal.mk_range_eq_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_range_eq_of_injective {α : Type u} {β : Type v} {f : α -> β} (hf : Inje
ctive f) : lift.{u} #(range f) = lift.{v} #α
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mk_range_eq_of_injective {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    lift.{u} #(range f) = lift.{v} #α :=
  lift_mk_eq'.mpr ⟨(Equiv.ofInjective f hf).symm⟩

@[deprecated mk_range_eq_of_injective (since := "2026-01-06")]
/-
**Cardinal.mk_range_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_range_eq_lift {α : Type u} {β : Type v} {f : α -> β} (hf : Injective f)
 : lift.{max u w} #(range f) = lift.{max v w} #α
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_eq`：lift_mk_eq {α : Type u} {β : Type v} : lift.{max v 
w} #α = lift.{max u w} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mk_range_eq_lift {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    lift.{max u w} #(range f) = lift.{max v w} #α :=
  lift_mk_eq.{v, u, w}.mpr ⟨(Equiv.ofInjective f hf).symm⟩
/-
**Cardinal.lift_mk_le_lift_mk_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：lift_mk_le_lift_mk_of_injective {α : Type u} {β : Type v} {f : α -> β} (hf
 : Injective f) : Cardinal.lift.{v} (#α) <= Cardinal.lift.{u} (#β)
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_range_eq_of_injective`：mk_range_eq_of_injective {α : Type u}
 {β : Type v} {f : α -> β} (hf : Injective f) : lift.{u} #(range f) = lift.{v} #
α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Cardinal.mk_set_le`：mk_set_le (s : Set α) : #s <= #α
-/
lemma lift_mk_le_lift_mk_of_injective {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    Cardinal.lift.{v} (#α) ≤ Cardinal.lift.{u} (#β) := by
  rw [← Cardinal.mk_range_eq_of_injective hf]
  exact Cardinal.lift_le.2 (Cardinal.mk_set_le _)
/-
**Cardinal.lift_mk_le_lift_mk_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`
。
形式化陈述：lift_mk_le_lift_mk_of_surjective {α : Type u} {β : Type v} {f : α -> β} (h
f : Surjective f) : Cardinal.lift.{u} (#β) <= Cardinal.lift.{v} (#α)
参数：hf : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.lift_mk_le_lift_mk_of_injective`：lift_mk_le_lift_mk_of_injectiv
e {α : Type u} {β : Type v} {f : α -> β} (hf : Injective f) : Cardinal.lift.{v} 
(#α) <= Cardinal.lift.{u} (#β)
· 使用定理 `Function.injective_surjInv`：injective_surjInv (h : Surjective f) : Injec
tive (surjInv h)
-/
lemma lift_mk_le_lift_mk_of_surjective {α : Type u} {β : Type v} {f : α → β} (hf : Surjective f) :
    Cardinal.lift.{u} (#β) ≤ Cardinal.lift.{v} (#α) :=
  lift_mk_le_lift_mk_of_injective (injective_surjInv hf)
/-
**Cardinal.mk_image_eq_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_image_eq_of_injOn {α β : Type u} (f : α -> β) (s : Set α) (h : InjOn f 
s) : #(f '' s) = #s
参数：f : α -> β；s : Set α；h : InjOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mk_image_eq_of_injOn {α β : Type u} (f : α → β) (s : Set α) (h : InjOn f s) :
    #(f '' s) = #s :=
  mk_congr (Equiv.Set.imageOfInjOn f s h).symm
/-
**Cardinal.mk_image_eq_of_injOn_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_image_eq_of_injOn_lift {α : Type u} {β : Type v} (f : α -> β) (s : Set 
α) (h : InjOn f s) : lift.{u} #(f '' s) = lift.{v} #s
参数：f : α -> β；s : Set α；h : InjOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_eq`：lift_mk_eq {α : Type u} {β : Type v} : lift.{max v 
w} #α = lift.{max u w} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mk_image_eq_of_injOn_lift {α : Type u} {β : Type v} (f : α → β) (s : Set α)
    (h : InjOn f s) : lift.{u} #(f '' s) = lift.{v} #s :=
  lift_mk_eq.{v, u, 0}.mpr ⟨(Equiv.Set.imageOfInjOn f s h).symm⟩
/-
**Cardinal.mk_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_image_eq {α β : Type u} {f : α -> β} {s : Set α} (hf : Injective f) : #
(f '' s) = #s
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_image_eq_of_injOn`：mk_image_eq_of_injOn {α β : Type u} (f : 
α -> β) (s : Set α) (h : InjOn f s) : #(f '' s) = #s
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem mk_image_eq {α β : Type u} {f : α → β} {s : Set α} (hf : Injective f) : #(f '' s) = #s :=
  mk_image_eq_of_injOn _ _ hf.injOn
/-
**Cardinal.mk_image_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_image_eq_lift {α : Type u} {β : Type v} (f : α -> β) (s : Set α) (h : I
njective f) : lift.{u} #(f '' s) = lift.{v} #s
参数：f : α -> β；s : Set α；h : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_image_eq_of_injOn_lift`：mk_image_eq_of_injOn_lift {α : Type 
u} {β : Type v} (f : α -> β) (s : Set α) (h : InjOn f s) : lift.{u} #(f '' s) = 
lift.{v} #s
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem mk_image_eq_lift {α : Type u} {β : Type v} (f : α → β) (s : Set α) (h : Injective f) :
    lift.{u} #(f '' s) = lift.{v} #s :=
  mk_image_eq_of_injOn_lift _ _ h.injOn

@[simp]
/-
**Cardinal.mk_image_embedding_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_image_embedding_lift {β : Type v} (f : α ↪ β) (s : Set α) : lift.{u} #(
f '' s) = lift.{v} #s
参数：f : α ↪ β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_image_eq_lift`：mk_image_eq_lift {α : Type u} {β : Type v} (f
 : α -> β) (s : Set α) (h : Injective f) : lift.{u} #(f '' s) = lift.{v} #s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem mk_image_embedding_lift {β : Type v} (f : α ↪ β) (s : Set α) :
    lift.{u} #(f '' s) = lift.{v} #s :=
  mk_image_eq_lift _ _ f.injective

@[simp]
/-
**Cardinal.mk_image_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_image_embedding (f : α ↪ β) (s : Set α) : #(f '' s) = #s
参数：f : α ↪ β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.mk_image_embedding_lift`：mk_image_embedding_lift {β : Type v} (
f : α ↪ β) (s : Set α) : lift.{u} #(f '' s) = lift.{v} #s
-/
theorem mk_image_embedding (f : α ↪ β) (s : Set α) : #(f '' s) = #s := by
  simpa using mk_image_embedding_lift f s
/-
**Cardinal.iSup_mk_le_mk_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：iSup_mk_le_mk_iUnion {α : Type u} {ι : Type v} {f : ι -> Set α} : ⨆ i, #(f
 i) <= #(⋃ i, f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
-/
theorem iSup_mk_le_mk_iUnion {α : Type u} {ι : Type v} {f : ι → Set α} :
    ⨆ i, #(f i) ≤ #(⋃ i, f i) :=
  ciSup_le' fun _ => mk_le_mk_of_subset (subset_iUnion _ _)
/-
**Cardinal.mk_iUnion_le_sum_mk** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_iUnion_le_sum_mk {α ι : Type u} {f : ι -> Set α} : #(⋃ i, f i) <= sum f
un i => #(f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_le_of_surjective`：mk_le_of_surjective {α β : Type u} {f : α 
-> β} (hf : Surjective f) : #β <= #α
· 使用定理 `Set.sigmaToiUnion_surjective`：sigmaToiUnion_surjective : Surjective (sig
maToiUnion t) | ⟨b, hb⟩ => have : exists a, b in t a
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
-/
theorem mk_iUnion_le_sum_mk {α ι : Type u} {f : ι → Set α} : #(⋃ i, f i) ≤ sum fun i => #(f i) :=
  calc
    #(⋃ i, f i) ≤ #(Σ i, f i) := mk_le_of_surjective (Set.sigmaToiUnion_surjective f)
    _ = sum fun i => #(f i) := mk_sigma _
/-
**Cardinal.mk_iUnion_le_sum_mk_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_iUnion_le_sum_mk_lift {α : Type u} {ι : Type v} {f : ι -> Set α} : lift
.{v} #(⋃ i, f i) <= sum fun i => #(f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_le_of_surjective`：mk_le_of_surjective {α β : Type u} {f : α 
-> β} (hf : Surjective f) : #β <= #α
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `ULift.up_surjective`：up_surjective : Surjective (@up α)
· 使用定理 `Set.sigmaToiUnion_surjective`：sigmaToiUnion_surjective : Surjective (sig
maToiUnion t) | ⟨b, hb⟩ => have : exists a, b in t a
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
-/
theorem mk_iUnion_le_sum_mk_lift {α : Type u} {ι : Type v} {f : ι → Set α} :
    lift.{v} #(⋃ i, f i) ≤ sum fun i => #(f i) :=
  calc
    lift.{v} #(⋃ i, f i) ≤ #(Σ i, f i) :=
      mk_le_of_surjective <| ULift.up_surjective.comp (Set.sigmaToiUnion_surjective f)
    _ = sum fun i => #(f i) := mk_sigma _
/-
**Cardinal.mk_iUnion_eq_sum_mk** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_iUnion_eq_sum_mk {α ι : Type u} {f : ι -> Set α} (h : Pairwise (Disjoin
t on f)) : #(⋃ i, f i) = sum fun i => #(f i)
参数：h : Pairwise (Disjoint on f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
-/
theorem mk_iUnion_eq_sum_mk {α ι : Type u} {f : ι → Set α}
    (h : Pairwise (Disjoint on f)) : #(⋃ i, f i) = sum fun i => #(f i) :=
  calc
    #(⋃ i, f i) = #(Σ i, f i) := mk_congr (Set.unionEqSigmaOfDisjoint h)
    _ = sum fun i => #(f i) := mk_sigma _
/-
**Cardinal.mk_iUnion_eq_sum_mk_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_iUnion_eq_sum_mk_lift {α : Type u} {ι : Type v} {f : ι -> Set α} (h : P
airwise (Disjoint on f)) : lift.{v} #(⋃ i, f i) = sum fun i => #(f i)
参数：h : Pairwise (Disjoint on f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
-/
theorem mk_iUnion_eq_sum_mk_lift {α : Type u} {ι : Type v} {f : ι → Set α}
    (h : Pairwise (Disjoint on f)) :
    lift.{v} #(⋃ i, f i) = sum fun i => #(f i) :=
  calc
    lift.{v} #(⋃ i, f i) = #(Σ i, f i) :=
      mk_congr <| .trans Equiv.ulift (Set.unionEqSigmaOfDisjoint h)
    _ = sum fun i => #(f i) := mk_sigma _
/-
**Cardinal.mk_iUnion_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_iUnion_le {α ι : Type u} (f : ι -> Set α) : #(⋃ i, f i) <= #ι * ⨆ i, #(
f i)
参数：f : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.mk_iUnion_le_sum_mk`：mk_iUnion_le_sum_mk {α ι : Type u} {f : ι 
-> Set α} : #(⋃ i, f i) <= sum fun i => #(f i)
· 使用定理 `Cardinal.sum_le_mk_mul_iSup`：sum_le_mk_mul_iSup {ι : Type u} (f : ι -> C
ardinal.{u}) : sum f <= #ι * ⨆ i, f i
-/
theorem mk_iUnion_le {α ι : Type u} (f : ι → Set α) : #(⋃ i, f i) ≤ #ι * ⨆ i, #(f i) :=
  mk_iUnion_le_sum_mk.trans (sum_le_mk_mul_iSup _)
/-
**Cardinal.mk_iUnion_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_iUnion_le_lift {α : Type u} {ι : Type v} (f : ι -> Set α) : lift.{v} #(
⋃ i, f i) <= lift.{u} #ι * ⨆ i, lift.{v} #(f i)
参数：f : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.mk_iUnion_le_sum_mk_lift`：mk_iUnion_le_sum_mk_lift {α : Type u}
 {ι : Type v} {f : ι -> Set α} : lift.{v} #(⋃ i, f i) <= sum fun i => #(f i)
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_sum`：lift_sum {ι : Type u} (f : ι -> Cardinal.{v}) : Cardi
nal.lift.{w} (Cardinal.sum f) = Cardinal.sum fun i => Cardinal.lift.{w} (f i)
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.sum_le_lift_mk_mul_iSup`：sum_le_lift_mk_mul_iSup {ι : Type u} (
f : ι -> Cardinal.{max u v}) : sum f <= lift #ι * ⨆ i, f i
-/
theorem mk_iUnion_le_lift {α : Type u} {ι : Type v} (f : ι → Set α) :
    lift.{v} #(⋃ i, f i) ≤ lift.{u} #ι * ⨆ i, lift.{v} #(f i) := by
  refine mk_iUnion_le_sum_mk_lift.trans <| Eq.trans_le ?_ (sum_le_lift_mk_mul_iSup _)
  rw [← lift_sum, lift_id'.{_, u}]
/-
**Cardinal.mk_sUnion_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_sUnion_le {α : Type u} (A : Set (Set α)) : #(⋃₀ A) <= #A * ⨆ s : A, #s
参数：A : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
· 使用定理 `Cardinal.mk_iUnion_le`：mk_iUnion_le {α ι : Type u} (f : ι -> Set α) : #(
⋃ i, f i) <= #ι * ⨆ i, #(f i)
-/
theorem mk_sUnion_le {α : Type u} (A : Set (Set α)) : #(⋃₀ A) ≤ #A * ⨆ s : A, #s := by
  rw [sUnion_eq_iUnion]
  apply mk_iUnion_le
/-
**Cardinal.mk_biUnion_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_biUnion_le {ι α : Type u} (A : ι -> Set α) (s : Set ι) : #(⋃ x in s, A 
x) <= #s * ⨆ x : s, #(A x.1)
参数：A : ι -> Set α；s : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `Cardinal.mk_iUnion_le`：mk_iUnion_le {α ι : Type u} (f : ι -> Set α) : #(
⋃ i, f i) <= #ι * ⨆ i, #(f i)
-/
theorem mk_biUnion_le {ι α : Type u} (A : ι → Set α) (s : Set ι) :
    #(⋃ x ∈ s, A x) ≤ #s * ⨆ x : s, #(A x.1) := by
  rw [biUnion_eq_iUnion]
  apply mk_iUnion_le
/-
**Cardinal.mk_biUnion_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_biUnion_le_lift {α : Type u} {ι : Type v} (A : ι -> Set α) (s : Set ι) 
: lift.{v} #(⋃ x in s, A x) <= lift.{u} #s * ⨆ x : s, lift.{v} #(A x.1)
参数：A : ι -> Set α；s : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `Cardinal.mk_iUnion_le_lift`：mk_iUnion_le_lift {α : Type u} {ι : Type v} 
(f : ι -> Set α) : lift.{v} #(⋃ i, f i) <= lift.{u} #ι * ⨆ i, lift.{v} #(f i)
-/
theorem mk_biUnion_le_lift {α : Type u} {ι : Type v} (A : ι → Set α) (s : Set ι) :
    lift.{v} #(⋃ x ∈ s, A x) ≤ lift.{u} #s * ⨆ x : s, lift.{v} #(A x.1) := by
  rw [biUnion_eq_iUnion]
  apply mk_iUnion_le_lift
/-
**Cardinal.finset_card_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：finset_card_lt_aleph0 (s : Finset α) : #(↑s : Set α) < ℵ₀
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lt_aleph0_of_finite`：lt_aleph0_of_finite (α : Type u) [Finite α
] : #α < ℵ₀
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem finset_card_lt_aleph0 (s : Finset α) : #(↑s : Set α) < ℵ₀ :=
  lt_aleph0_of_finite _
/-
**Cardinal.mk_set_eq_nat_iff_finset** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_set_eq_nat_iff_finset {α} {s : Set α} {n : Nat} : #s = n ↔ exists t : F
inset α, (t : Set α) = s ∧ t.card = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0_iff_set_finite`：lt_aleph0_iff_set_finite {S : Set α} 
: #S < ℵ₀ ↔ S.Finite
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Cardinal.mk_coe_finset`：mk_coe_finset {α : Type u} {s : Finset α} : #s =
 ↑(Finset.card s)
-/
theorem mk_set_eq_nat_iff_finset {α} {s : Set α} {n : ℕ} :
    #s = n ↔ ∃ t : Finset α, (t : Set α) = s ∧ t.card = n := by
  constructor
  · intro h
    lift s to Finset α using lt_aleph0_iff_set_finite.1 (h.symm ▸ natCast_lt_aleph0)
    simpa using h
  · rintro ⟨t, rfl, rfl⟩
    exact mk_coe_finset
/-
**Cardinal.mk_eq_nat_iff_finset** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_eq_nat_iff_finset {n : Nat} : #α = n ↔ exists t : Finset α, (t : Set α)
 = univ ∧ t.card = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_univ`：mk_univ {α : Type u} : #(@univ α) = #α
· 使用定理 `Cardinal.mk_set_eq_nat_iff_finset`：mk_set_eq_nat_iff_finset {α} {s : Set
 α} {n : Nat} : #s = n ↔ exists t : Finset α, (t : Set α) = s ∧ t.card = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_eq_nat_iff_finset {n : ℕ} :
    #α = n ↔ ∃ t : Finset α, (t : Set α) = univ ∧ t.card = n := by
  rw [← mk_univ, mk_set_eq_nat_iff_finset]
/-
**Cardinal.mk_eq_nat_iff_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_eq_nat_iff_fintype {n : Nat} : #α = n ↔ exists h : Fintype α, @Fintype.
card α h = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_eq_nat_iff_finset`：mk_eq_nat_iff_finset {n : Nat} : #α = n ↔
 exists t : Finset α, (t : Set α) = univ ∧ t.card = n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem mk_eq_nat_iff_fintype {n : ℕ} : #α = n ↔ ∃ h : Fintype α, @Fintype.card α h = n := by
  rw [mk_eq_nat_iff_finset]
  constructor
  · rintro ⟨t, ht, hn⟩
    exact ⟨⟨t, eq_univ_iff_forall.1 ht⟩, hn⟩
  · rintro ⟨⟨t, ht⟩, hn⟩
    exact ⟨t, eq_univ_iff_forall.2 ht, hn⟩
/-
**Cardinal.mk_set_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_set_eq_one_iff {s : Set α} : #s = 1 ↔ exists x, s = {x}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.eq_one_iff_unique`：eq_one_iff_unique {α : Type*} : #α = 1 ↔ Sub
singleton α ∧ Nonempty α
· 使用定理 `Set.exists_eq_singleton_iff_nonempty_subsingleton`：exists_eq_singleton_i
ff_nonempty_subsingleton : (exists a : α, s = {a}) ↔ s.Nonempty ∧ s.Subsingleton
· 使用定理 `Set.nonempty_coe_sort`：nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.N
onempty
· 使用定理 `Set.subsingleton_coe`：subsingleton_coe (s : Set α) : Subsingleton s ↔ s.
Subsingleton
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_set_eq_one_iff {s : Set α} : #s = 1 ↔ ∃ x, s = {x} := by
  rw [eq_one_iff_unique, Set.exists_eq_singleton_iff_nonempty_subsingleton,
    Set.nonempty_coe_sort, Set.subsingleton_coe, and_comm]
/-
**Cardinal.mk_union_add_mk_inter** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_union_add_mk_inter {α : Type u} {S T : Set α} : #(S union T : Set α) + 
#(S inter T : Set α) = #S + #T
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_union_add_mk_inter {α : Type u} {S T : Set α} :
    #(S ∪ T : Set α) + #(S ∩ T : Set α) = #S + #T := by
  classical
  exact Quot.sound ⟨Equiv.Set.unionSumInter S T⟩

/-- The cardinality of a union is at most the sum of the cardinalities
of the two sets. -/
/-
**Cardinal.mk_union_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_union_le {α : Type u} (S T : Set α) : #(S union T : Set α) <= #S + #T
参数：S T : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `self_le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] (a b : α), a ≤ a + b
· 使用定理 `Cardinal.mk_union_add_mk_inter`：mk_union_add_mk_inter {α : Type u} {S T 
: Set α} : #(S union T : Set α) + #(S inter T : Set α) = #S + #T

--- 原说明 ---
The cardinality of a union is at most the sum of the cardinalities
of the two sets.
-/
theorem mk_union_le {α : Type u} (S T : Set α) : #(S ∪ T : Set α) ≤ #S + #T :=
  @mk_union_add_mk_inter α S T ▸ self_le_add_right #(S ∪ T : Set α) #(S ∩ T : Set α)
/-
**Cardinal.mk_union_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_union_of_disjoint {α : Type u} {S T : Set α} (H : Disjoint S T) : #(S u
nion T : Set α) = #S + #T
参数：H : Disjoint S T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_union_of_disjoint {α : Type u} {S T : Set α} (H : Disjoint S T) :
    #(S ∪ T : Set α) = #S + #T := by
  classical
  exact Quot.sound ⟨Equiv.Set.union H⟩
/-
**Cardinal.mk_insert** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_insert {α : Type u} {s : Set α} {a : α} (h : a ∉ s) : #(insert a s : Se
t α) = #s + 1
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Cardinal.mk_union_of_disjoint`：mk_union_of_disjoint {α : Type u} {S T : 
Set α} (H : Disjoint S T) : #(S union T : Set α) = #S + #T
· 使用定理 `Cardinal.mk_singleton`：mk_singleton {α : Type u} (x : α) : #({x} : Set α
) = 1
-/
theorem mk_insert {α : Type u} {s : Set α} {a : α} (h : a ∉ s) :
    #(insert a s : Set α) = #s + 1 := by
  rw [← union_singleton, mk_union_of_disjoint, mk_singleton]
  simpa
/-
**Cardinal.mk_insert_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_insert_le {α : Type u} {s : Set α} {a : α} : #(insert a s : Set α) <= #
s + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Cardinal.mk_insert`：mk_insert {α : Type u} {s : Set α} {a : α} (h : a ∉ 
s) : #(insert a s : Set α) = #s + 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mk_insert_le {α : Type u} {s : Set α} {a : α} : #(insert a s : Set α) ≤ #s + 1 := by
  by_cases h : a ∈ s
  · simp only [insert_eq_of_mem h, self_le_add_right]
  · rw [mk_insert h]
/-
**Cardinal.mk_sum_compl** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_sum_compl {α} (s : Set α) : #s + #(sᶜ : Set α) = #α
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
-/
theorem mk_sum_compl {α} (s : Set α) : #s + #(sᶜ : Set α) = #α := by
  classical
  exact mk_congr (Equiv.Set.sumCompl s)
/-
**Cardinal.mk_le_iff_forall_finset_subset_card_le** 是 Mathlib 中的一个定理，位于命名空间 `Car
dinal`。
形式化陈述：mk_le_iff_forall_finset_subset_card_le {α : Type u} {n : Nat} {t : Set α} 
: #t <= n ↔ forall s : Finset α, (s : Set α) subseteq t -> s.card <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Cardinal.card_le_of`：card_le_of {α : Type u} {n : Nat} (H : forall s : F
inset α, s.card <= n) : #α <= n
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem mk_le_iff_forall_finset_subset_card_le {α : Type u} {n : ℕ} {t : Set α} :
    #t ≤ n ↔ ∀ s : Finset α, (s : Set α) ⊆ t → s.card ≤ n := by
  refine ⟨fun H s hs ↦ by simpa using (mk_le_mk_of_subset hs).trans H, fun H ↦ ?_⟩
  apply card_le_of (fun s ↦ ?_)
  classical
  let u : Finset α := s.image Subtype.val
  have : u.card = s.card := Finset.card_image_of_injOn Subtype.coe_injective.injOn
  grind
/-
**Cardinal.mk_subtype_mono** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_subtype_mono {p q : α -> Prop} (h : forall x, p x -> q x) : #{ x // p x
 } <= #{ x // q x }
参数：h : forall x, p x -> q x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_subtype_mono {p q : α → Prop} (h : ∀ x, p x → q x) :
    #{ x // p x } ≤ #{ x // q x } :=
  ⟨embeddingOfSubset _ _ h⟩
/-
**Cardinal.card_lt_card_of_right_finite** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：card_lt_card_of_right_finite {A B : Set α} (hfin : B.Finite) (hlt : A ⊂ B)
 : #A < #B
参数：hfin : B.Finite；hlt : A ⊂ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.toFinset_ssubset_toFinset`：toFinset_ssubset_toFinset [Fintype s] [Fi
ntype t] : s.toFinset ⊂ t.toFinset ↔ s ⊂ t
-/
lemma card_lt_card_of_right_finite {A B : Set α} (hfin : B.Finite) (hlt : A ⊂ B) : #A < #B := by
  have : Fintype A := (hfin.subset hlt.subset).fintype
  have : Fintype B := hfin.fintype
  simpa using Finset.card_lt_card <| Set.toFinset_ssubset_toFinset.mpr hlt
/-
**Cardinal.card_lt_card_of_left_finite** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：card_lt_card_of_left_finite {A B : Set α} (hfin : A.Finite) (hlt : A ⊂ B) 
: #A < #B
参数：hfin : A.Finite；hlt : A ⊂ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用引理 `Cardinal.card_lt_card_of_right_finite`：card_lt_card_of_right_finite {A B
 : Set α} (hfin : B.Finite) (hlt : A ⊂ B) : #A < #B
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lt_aleph0_iff_subtype_finite`：lt_aleph0_iff_subtype_finite {p :
 α -> Prop} : #{ x // p x } < ℵ₀ ↔ { x | p x }.Finite
· 使用引理 `Cardinal.aleph0_le_mk_iff`：aleph0_le_mk_iff : ℵ₀ <= #α ↔ Infinite α
-/
lemma card_lt_card_of_left_finite {A B : Set α} (hfin : A.Finite) (hlt : A ⊂ B) : #A < #B := by
  rcases finite_or_infinite B with hfin | hinf
  · exact card_lt_card_of_right_finite hfin hlt
  · exact (lt_aleph0_iff_subtype_finite.mpr hfin).trans_le <| Cardinal.aleph0_le_mk_iff.mpr hinf
/-
**Cardinal.mk_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_strictMono [Finite α] : StrictMono (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.card_lt_card_of_right_finite`：card_lt_card_of_right_finite {A B
 : Set α} (hfin : B.Finite) (hlt : A ⊂ B) : #A < #B
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
theorem mk_strictMono [Finite α] : StrictMono (α := Set α) (mk ∘ (↑)) :=
  fun _ s ↦ card_lt_card_of_right_finite s.toFinite
/-
**Cardinal.mk_strictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_strictMonoOn : StrictMonoOn (mk ∘ (↑)) {s : Set α | s.Finite}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.card_lt_card_of_right_finite`：card_lt_card_of_right_finite {A B
 : Set α} (hfin : B.Finite) (hlt : A ⊂ B) : #A < #B
-/
theorem mk_strictMonoOn : StrictMonoOn (mk ∘ (↑)) {s : Set α | s.Finite} :=
  fun _ _ _ ↦ card_lt_card_of_right_finite
/-
**Cardinal.le_mk_sdiff_add_mk** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：le_mk_sdiff_add_mk (S T : Set α) : #S <= #(S \ T : Set α) + #T
参数：S T : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Set.subset_sdiff_union`：subset_sdiff_union (s t : Set α) : s subseteq s 
\ t union t
· 使用定理 `Cardinal.mk_union_le`：mk_union_le {α : Type u} (S T : Set α) : #(S union
 T : Set α) <= #S + #T
-/
theorem le_mk_sdiff_add_mk (S T : Set α) : #S ≤ #(S \ T : Set α) + #T :=
  (mk_le_mk_of_subset <| subset_sdiff_union _ _).trans <| mk_union_le _ _

@[deprecated (since := "2026-06-03")] alias le_mk_diff_add_mk := le_mk_sdiff_add_mk
/-
**Cardinal.mk_sdiff_add_mk** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_sdiff_add_mk {S T : Set α} (h : T subseteq S) : #(S \ T : Set α) + #T =
 #S
参数：h : T subseteq S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_union_of_disjoint`：mk_union_of_disjoint {α : Type u} {S T : 
Set α} (H : Disjoint S T) : #(S union T : Set α) = #S + #T
· 使用定理 `disjoint_sdiff_self_left`：disjoint_sdiff_self_left : Disjoint (y \ x) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_union_of_subset`：sdiff_union_of_subset {s t : Set α} (h : t su
bseteq s) : s \ t union t = s
-/
theorem mk_sdiff_add_mk {S T : Set α} (h : T ⊆ S) : #(S \ T : Set α) + #T = #S := by
  refine (mk_union_of_disjoint <| ?_).symm.trans <| by rw [sdiff_union_of_subset h]
  exact disjoint_sdiff_self_left

@[deprecated (since := "2026-06-03")] alias mk_diff_add_mk := mk_sdiff_add_mk
/-
**Cardinal.sdiff_nonempty_of_mk_lt_mk** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：sdiff_nonempty_of_mk_lt_mk {S T : Set α} (h : #S < #T) : (T \ S).Nonempty
参数：h : #S < #T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_set_ne_zero_iff`：mk_set_ne_zero_iff {s : Set α} : #s != 0 ↔ 
s.Nonempty
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.le_mk_sdiff_add_mk`：le_mk_sdiff_add_mk (S T : Set α) : #S <= #(
S \ T : Set α) + #T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma sdiff_nonempty_of_mk_lt_mk {S T : Set α} (h : #S < #T) : (T \ S).Nonempty := by
  rw [← mk_set_ne_zero_iff]
  intro h'
  exact h.not_ge ((le_mk_sdiff_add_mk T S).trans (by simp [h']))

@[deprecated (since := "2026-06-03")] alias diff_nonempty_of_mk_lt_mk := sdiff_nonempty_of_mk_lt_mk
/-
**Cardinal.compl_nonempty_of_mk_lt_mk** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：compl_nonempty_of_mk_lt_mk {S : Set α} (h : #S < #α) : Sᶜ.Nonempty
参数：h : #S < #α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用引理 `Cardinal.sdiff_nonempty_of_mk_lt_mk`：sdiff_nonempty_of_mk_lt_mk {S T : S
et α} (h : #S < #T) : (T \ S).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_univ`：mk_univ {α : Type u} : #(@univ α) = #α
-/
lemma compl_nonempty_of_mk_lt_mk {S : Set α} (h : #S < #α) : Sᶜ.Nonempty := by
  rw [← mk_univ (α := α)] at h
  simpa [Set.compl_eq_univ_sdiff] using sdiff_nonempty_of_mk_lt_mk h
/-
**Cardinal.mk_union_le_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_union_le_aleph0 {α} {P Q : Set α} : #(P union Q : Set α) <= ℵ₀ ↔ #P <= 
ℵ₀ ∧ #Q <= ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk_union_le_aleph0 {α} {P Q : Set α} :
    #(P ∪ Q : Set α) ≤ ℵ₀ ↔ #P ≤ ℵ₀ ∧ #Q ≤ ℵ₀ := by
  simp only [le_aleph0_iff_subtype_countable, ofPred_mem_eq, Set.union_def,
    ← countable_union]
/-
**Cardinal.mk_sep** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_sep (s : Set α) (t : α -> Prop) : #({ x in s | t x } : Set α) = #{ x : 
s | t x.1 }
参数：s : Set α；t : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
-/
theorem mk_sep (s : Set α) (t : α → Prop) : #({ x ∈ s | t x } : Set α) = #{ x : s | t x.1 } :=
  mk_congr (Equiv.Set.sep s t)
/-
**Cardinal.mk_preimage_of_injective_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_preimage_of_injective_lift {α : Type u} {β : Type v} (f : α -> β) (s : 
Set β) (h : Injective f) : lift.{v} #(f ⁻¹' s) <= lift.{u} #s
参数：f : α -> β；s : Set β；h : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_mk_le`：lift_mk_le {α : Type v} {β : Type w} : lift.{max u 
w} #α <= lift.{max u v} #β ↔ Nonempty (α ↪ β)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.coind_injective`：coind_injective {α β} {f : α -> β} {p : β -> Pr
op} (h : forall a, p (f a)) (hf : Injective f) : Injective (coind f h)
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
theorem mk_preimage_of_injective_lift {α : Type u} {β : Type v} (f : α → β) (s : Set β)
    (h : Injective f) : lift.{v} #(f ⁻¹' s) ≤ lift.{u} #s := by
  rw [lift_mk_le.{0}]
  use Subtype.coind (fun x => f x.1) fun x => mem_preimage.mp x.2
  apply Subtype.coind_injective; exact h.comp Subtype.val_injective
/-
**Cardinal.mk_preimage_of_subset_range_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`
。
形式化陈述：mk_preimage_of_subset_range_lift {α : Type u} {β : Type v} (f : α -> β) (s
 : Set β) (h : s subseteq range f) : lift.{u} #s <= lift.{v} #(f ⁻¹' s)
参数：f : α -> β；s : Set β；h : s subseteq range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq_iff`：image_preimage_eq_iff {f : α -> β} {s : Set β
} : f '' f ⁻¹' s = s ↔ s subseteq range f
· 使用定理 `Cardinal.mk_image_le_lift`：mk_image_le_lift {α : Type u} {β : Type v} {f
 : α -> β} {s : Set α} : lift.{u} #(f '' s) <= lift.{v} #s
-/
theorem mk_preimage_of_subset_range_lift {α : Type u} {β : Type v} (f : α → β) (s : Set β)
    (h : s ⊆ range f) : lift.{u} #s ≤ lift.{v} #(f ⁻¹' s) := by
  rw [← image_preimage_eq_iff] at h
  nth_rewrite 1 [← h]
  apply mk_image_le_lift
/-
**Cardinal.mk_preimage_of_injective_of_subset_range_lift** 是 Mathlib 中的一个定理，位于命名
空间 `Cardinal`。
形式化陈述：mk_preimage_of_injective_of_subset_range_lift {β : Type v} (f : α -> β) (s
 : Set β) (h : Injective f) (h2 : s subseteq range f) : lift.{v} #(f ⁻¹' s) = li
ft.{u} #s
参数：f : α -> β；s : Set β；h : Injective f；h2 : s subseteq range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Cardinal.mk_preimage_of_injective_lift`：mk_preimage_of_injective_lift {α
 : Type u} {β : Type v} (f : α -> β) (s : Set β) (h : Injective f) : lift.{v} #(
f ⁻¹' s) <= lift.{u} #s
· 使用定理 `Cardinal.mk_preimage_of_subset_range_lift`：mk_preimage_of_subset_range_l
ift {α : Type u} {β : Type v} (f : α -> β) (s : Set β) (h : s subseteq range f) 
: lift.{u} #s <= lift.{v} #(f ⁻…
-/
theorem mk_preimage_of_injective_of_subset_range_lift {β : Type v} (f : α → β) (s : Set β)
    (h : Injective f) (h2 : s ⊆ range f) : lift.{v} #(f ⁻¹' s) = lift.{u} #s :=
  le_antisymm (mk_preimage_of_injective_lift f s h) (mk_preimage_of_subset_range_lift f s h2)
/-
**Cardinal.mk_preimage_of_injective_of_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `C
ardinal`。
形式化陈述：mk_preimage_of_injective_of_subset_range (f : α -> β) (s : Set β) (h : Inj
ective f) (h2 : s subseteq range f) : #(f ⁻¹' s) = #s
参数：f : α -> β；s : Set β；h : Injective f；h2 : s subseteq range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.mk_preimage_of_injective_of_subset_range_lift`：mk_preimage_of_i
njective_of_subset_range_lift {β : Type v} (f : α -> β) (s : Set β) (h : Injecti
ve f) (h2 : s subseteq range f) : lift.{v} #…
-/
theorem mk_preimage_of_injective_of_subset_range (f : α → β) (s : Set β) (h : Injective f)
    (h2 : s ⊆ range f) : #(f ⁻¹' s) = #s := by
  convert! mk_preimage_of_injective_of_subset_range_lift.{u, u} f s h h2 using 1 <;> rw [lift_id]

@[simp]
/-
**Cardinal.mk_preimage_equiv_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_preimage_equiv_lift {β : Type v} (f : α ≃ β) (s : Set β) : lift.{v} #(f
 ⁻¹' s) = lift.{u} #s
参数：f : α ≃ β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_preimage_of_injective_of_subset_range_lift`：mk_preimage_of_i
njective_of_subset_range_lift {β : Type v} (f : α -> β) (s : Set β) (h : Injecti
ve f) (h2 : s subseteq range f) : lift.{v} #…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.range_eq_univ`：range_eq_univ (e : α ≃ β) : range e = univ
-/
theorem mk_preimage_equiv_lift {β : Type v} (f : α ≃ β) (s : Set β) :
    lift.{v} #(f ⁻¹' s) = lift.{u} #s := by
  apply mk_preimage_of_injective_of_subset_range_lift _ _ f.injective
  rw [f.range_eq_univ]
  exact fun _ _ ↦ ⟨⟩

@[simp]
/-
**Cardinal.mk_preimage_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_preimage_equiv (f : α ≃ β) (s : Set β) : #(f ⁻¹' s) = #s
参数：f : α ≃ β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.mk_preimage_equiv_lift`：mk_preimage_equiv_lift {β : Type v} (f 
: α ≃ β) (s : Set β) : lift.{v} #(f ⁻¹' s) = lift.{u} #s
-/
theorem mk_preimage_equiv (f : α ≃ β) (s : Set β) : #(f ⁻¹' s) = #s := by
  simpa using mk_preimage_equiv_lift f s
/-
**Cardinal.mk_preimage_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_preimage_of_injective (f : α -> β) (s : Set β) (h : Injective f) : #(f 
⁻¹' s) <= #s
参数：f : α -> β；s : Set β；h : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.mk_preimage_of_injective_lift`：mk_preimage_of_injective_lift {α
 : Type u} {β : Type v} (f : α -> β) (s : Set β) (h : Injective f) : lift.{v} #(
f ⁻¹' s) <= lift.{u} #s
-/
theorem mk_preimage_of_injective (f : α → β) (s : Set β) (h : Injective f) :
    #(f ⁻¹' s) ≤ #s := by
  rw [← lift_id #(↑(f ⁻¹' s)), ← lift_id #(↑s)]
  exact mk_preimage_of_injective_lift f s h
/-
**Cardinal.mk_preimage_of_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_preimage_of_subset_range (f : α -> β) (s : Set β) (h : s subseteq range
 f) : #s <= #(f ⁻¹' s)
参数：f : α -> β；s : Set β；h : s subseteq range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.mk_preimage_of_subset_range_lift`：mk_preimage_of_subset_range_l
ift {α : Type u} {β : Type v} (f : α -> β) (s : Set β) (h : s subseteq range f) 
: lift.{u} #s <= lift.{v} #(f ⁻…
-/
theorem mk_preimage_of_subset_range (f : α → β) (s : Set β) (h : s ⊆ range f) :
    #s ≤ #(f ⁻¹' s) := by
  rw [← lift_id #(↑(f ⁻¹' s)), ← lift_id #(↑s)]
  exact mk_preimage_of_subset_range_lift f s h
/-
**Cardinal.mk_subset_ge_of_subset_image_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal
`。
形式化陈述：mk_subset_ge_of_subset_image_lift {α : Type u} {β : Type v} (f : α -> β) {
s : Set α} {t : Set β} (h : t subseteq f '' s) : lift.{u} #t <= lift.{v} #({ x i
n s | f x in t } : Set α)
参数：f : α -> β；h : t subseteq f '' s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_sep`：mk_sep (s : Set α) (t : α -> Prop) : #({ x in s | t x }
 : Set α) = #{ x : s | t x.1 }
· 使用定理 `Cardinal.mk_preimage_of_subset_range_lift`：mk_preimage_of_subset_range_l
ift {α : Type u} {β : Type v} (f : α -> β) (s : Set β) (h : s subseteq range f) 
: lift.{u} #s <= lift.{v} #(f ⁻…
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
-/
theorem mk_subset_ge_of_subset_image_lift {α : Type u} {β : Type v} (f : α → β) {s : Set α}
    {t : Set β} (h : t ⊆ f '' s) : lift.{u} #t ≤ lift.{v} #({ x ∈ s | f x ∈ t } : Set α) := by
  rw [image_eq_range] at h
  convert! mk_preimage_of_subset_range_lift _ _ h using 1
  rw [mk_sep]
  rfl
/-
**Cardinal.mk_subset_ge_of_subset_image** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_subset_ge_of_subset_image (f : α -> β) {s : Set α} {t : Set β} (h : t s
ubseteq f '' s) : #t <= #({ x in s | f x in t } : Set α)
参数：f : α -> β；h : t subseteq f '' s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_sep`：mk_sep (s : Set α) (t : α -> Prop) : #({ x in s | t x }
 : Set α) = #{ x : s | t x.1 }
· 使用定理 `Cardinal.mk_preimage_of_subset_range`：mk_preimage_of_subset_range (f : α
 -> β) (s : Set β) (h : s subseteq range f) : #s <= #(f ⁻¹' s)
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
-/
theorem mk_subset_ge_of_subset_image (f : α → β) {s : Set α} {t : Set β} (h : t ⊆ f '' s) :
    #t ≤ #({ x ∈ s | f x ∈ t } : Set α) := by
  rw [image_eq_range] at h
  convert! mk_preimage_of_subset_range _ _ h using 1
  rw [mk_sep]
  rfl
/-
**Cardinal.le_mk_iff_exists_subset** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：le_mk_iff_exists_subset {c : Cardinal} {α : Type u} {s : Set α} : c <= #s 
↔ exists p : Set α, p subseteq s ∧ #p = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.le_mk_iff_exists_set`：le_mk_iff_exists_set {c : Cardinal} {α : 
Type u} : c <= #α ↔ exists p : Set α, #p = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.exists_set_subtype`：exists_set_subtype {t : Set α} (p : Set α ->
 Prop) : (exists s : Set t, p (((↑) : t -> α) '' s)) ↔ exists s : Set α, s subse
teq t ∧ p s
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Cardinal.mk_image_eq`：mk_image_eq {α β : Type u} {f : α -> β} {s : Set α
} (hf : Injective f) : #(f '' s) = #s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_mk_iff_exists_subset {c : Cardinal} {α : Type u} {s : Set α} :
    c ≤ #s ↔ ∃ p : Set α, p ⊆ s ∧ #p = c := by
  rw [le_mk_iff_exists_set, ← Subtype.exists_set_subtype]
  apply exists_congr; intro t; rw [mk_image_eq]; apply Subtype.val_injective

@[simp]
/-
**Cardinal.mk_range_inl** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_range_inl {α : Type u} {β : Type v} : #(range (@Sum.inl α β)) = lift.{v
} #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Equiv.lift_cardinal_eq`：∀ {α : Type u} {β : Type v} (e : α ≃ β), Cardina
l.lift.{v, u} (Cardinal.mk α) = Cardinal.lift.{u, v} (Cardinal.mk β)
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
-/
theorem mk_range_inl {α : Type u} {β : Type v} : #(range (@Sum.inl α β)) = lift.{v} #α := by
  rw [← lift_id'.{u, v} #_, (Equiv.Set.rangeInl α β).lift_cardinal_eq, lift_umax.{u, v}]

@[simp]
/-
**Cardinal.mk_range_inr** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_range_inr {α : Type u} {β : Type v} : #(range (@Sum.inr α β)) = lift.{u
} #β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Equiv.lift_cardinal_eq`：∀ {α : Type u} {β : Type v} (e : α ≃ β), Cardina
l.lift.{v, u} (Cardinal.mk α) = Cardinal.lift.{u, v} (Cardinal.mk β)
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
-/
theorem mk_range_inr {α : Type u} {β : Type v} : #(range (@Sum.inr α β)) = lift.{u} #β := by
  rw [← lift_id'.{v, u} #_, (Equiv.Set.rangeInr α β).lift_cardinal_eq, lift_umax.{v, u}]
/-
**Cardinal.two_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：two_le_iff : (2 : Cardinal) <= #α ↔ exists x y : α, x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Cardinal.two_le_iff_one_lt`：two_le_iff_one_lt {c : Cardinal} : 2 <= c ↔ 
1 < c
· 使用定理 `Cardinal.one_lt_iff_nontrivial`：one_lt_iff_nontrivial {α : Type u} : 1 <
 #α ↔ Nontrivial α
· 使用定理 `nontrivial_iff`：nontrivial_iff : Nontrivial α ↔ exists x y : α, x != y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem two_le_iff : (2 : Cardinal) ≤ #α ↔ ∃ x y : α, x ≠ y := by
  rw [two_le_iff_one_lt, one_lt_iff_nontrivial, nontrivial_iff]
/-
**Cardinal.two_le_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：two_le_iff' (x : α) : (2 : Cardinal) <= #α ↔ exists y : α, y != x
参数：x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.two_le_iff`：two_le_iff : (2 : Cardinal) <= #α ↔ exists x y : α,
 x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nontrivial_iff`：nontrivial_iff : Nontrivial α ↔ exists x y : α, x != y
· 使用定理 `nontrivial_iff_exists_ne`：nontrivial_iff_exists_ne (x : α) : Nontrivial 
α ↔ exists y, y != x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem two_le_iff' (x : α) : (2 : Cardinal) ≤ #α ↔ ∃ y : α, y ≠ x := by
  rw [two_le_iff, ← nontrivial_iff, nontrivial_iff_exists_ne x]
/-
**Cardinal.mk_eq_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_eq_two_iff : #α = 2 ↔ exists x y : α, x != y ∧ ({x, y} : Set α) = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mk_eq_two_iff : #α = 2 ↔ ∃ x y : α, x ≠ y ∧ ({x, y} : Set α) = univ := by
  classical
  simp only [← @Nat.cast_two Cardinal, mk_eq_nat_iff_finset, Finset.card_eq_two]
  constructor
  · rintro ⟨t, ht, x, y, hne, rfl⟩
    exact ⟨x, y, hne, by simpa using ht⟩
  · rintro ⟨x, y, hne, h⟩
    exact ⟨{x, y}, by simpa using h, x, y, hne, rfl⟩
/-
**Cardinal.mk_eq_two_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_eq_two_iff' (x : α) : #α = 2 ↔ exists! y, y != x
参数：x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_eq_two_iff`：mk_eq_two_iff : #α = 2 ↔ exists x y : α, x != y 
∧ ({x, y} : Set α) = univ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
-/
theorem mk_eq_two_iff' (x : α) : #α = 2 ↔ ∃! y, y ≠ x := by
  rw [mk_eq_two_iff]; constructor
  · rintro ⟨a, b, hne, h⟩
    simp only [eq_univ_iff_forall, mem_insert_iff, mem_singleton_iff] at h
    rcases h x with (rfl | rfl)
    exacts [⟨b, hne.symm, fun z => (h z).resolve_left⟩, ⟨a, hne, fun z => (h z).resolve_right⟩]
  · rintro ⟨y, hne, hy⟩
    exact ⟨x, y, hne.symm, eq_univ_of_forall fun z => or_iff_not_imp_left.2 (hy z)⟩
/-
**Cardinal.exists_notMem_of_length_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：exists_notMem_of_length_lt {α : Type*} (l : List α) (h : ↑l.length < #α) :
 exists z : α, z ∉ l
参数：l : List α；h : ↑l.length < #α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_univ`：mk_univ {α : Type u} : #(@univ α) = #α
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_toFinset`：mem_toFinset : a in l.toFinset ↔ a in l
· 使用定理 `Cardinal.mk_coe_finset`：mk_coe_finset {α : Type u} {s : Finset α} : #s =
 ↑(Finset.card s)
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `List.toFinset_card_le`：List.toFinset_card_le : #l.toFinset <= l.length
-/
theorem exists_notMem_of_length_lt {α : Type*} (l : List α) (h : ↑l.length < #α) :
    ∃ z : α, z ∉ l := by
  classical
  contrapose! h
  calc
    #α = #(Set.univ : Set α) := mk_univ.symm
    _ ≤ #l.toFinset := mk_le_mk_of_subset fun x _ => List.mem_toFinset.mpr (h x)
    _ = l.toFinset.card := Cardinal.mk_coe_finset
    _ ≤ l.length := Nat.cast_le.mpr (List.toFinset_card_le l)
/-
**Cardinal.exists_ne_ne_of_three_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：exists_ne_ne_of_three_le {α : Type*} (h : 3 <= #α) (x y : α) : exists z : 
α, z != x ∧ z != y
参数：h : 3 <= #α；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Cardinal.natCast_add_one_le_iff`：natCast_add_one_le_iff {n : Nat} {c : C
ardinal} : n + 1 <= c ↔ n < c
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `Cardinal.exists_notMem_of_length_lt`：exists_notMem_of_length_lt {α : Typ
e*} (l : List α) (h : ↑l.length < #α) : exists z : α, z ∉ l
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem exists_ne_ne_of_three_le {α : Type*} (h : 3 ≤ #α) (x y : α) : ∃ z : α, z ≠ x ∧ z ≠ y := by
  have : ↑(3 : ℕ) ≤ #α := by simpa using h
  have : ↑(2 : ℕ) < #α := by rwa [← natCast_add_one_le_iff, ← Nat.cast_add_one]
  have := exists_notMem_of_length_lt [x, y] this
  simpa [not_or] using this

@[deprecated (since := "2026-02-17")] alias three_le := exists_ne_ne_of_three_le

/-! ### `powerlt` operation -/

/-- The function `a ^< b`, defined as the supremum of `a ^ c` for `c < b`. -/
/-
**Cardinal.powerlt** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：powerlt (a b : Cardinal.{u}) : Cardinal.{u}
参数：a b : Cardinal.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `a ^< b`, defined as the supremum of `a ^ c` for `c < b`.
-/
def powerlt (a b : Cardinal.{u}) : Cardinal.{u} :=
  ⨆ c : Iio b, a ^ (c : Cardinal)

@[inherit_doc]
infixl:80 " ^< " => powerlt
/-
**Cardinal.le_powerlt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：le_powerlt {b c : Cardinal.{u}} (a) (h : c < b) : (a ^ c) <= a ^< b
参数：a；h : c < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Cardinal.bddAbove_image`：bddAbove_image (f : Cardinal.{u} -> Cardinal.{m
ax u v}) {s : Set Cardinal.{u}} (hs : BddAbove s) : BddAbove (f '' s)
· 使用定理 `bddAbove_Iio`：bddAbove_Iio : BddAbove (Iio a)
-/
theorem le_powerlt {b c : Cardinal.{u}} (a) (h : c < b) : (a ^ c) ≤ a ^< b := by
  refine le_ciSup (f := fun y : Iio b => a ^ (y : Cardinal)) ?_ ⟨c, h⟩
  rw [← image_eq_range]
  exact bddAbove_image.{u, u} _ bddAbove_Iio
/-
**Cardinal.powerlt_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：powerlt_le {a b c : Cardinal.{u}} : a ^< b <= c ↔ forall x < b, a ^ x <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.powerlt.eq_1`：∀ (a b : Cardinal.{u}), a ^< b = ⨆ c, a ^ ↑c
· 使用定理 `ciSup_le_iff'`：ciSup_le_iff' {f : ι -> α} (h : BddAbove (range f)) {a : 
α} : ⨆ i, f i <= a ↔ forall i, f i <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Cardinal.bddAbove_image`：bddAbove_image (f : Cardinal.{u} -> Cardinal.{m
ax u v}) {s : Set Cardinal.{u}} (hs : BddAbove s) : BddAbove (f '' s)
· 使用定理 `bddAbove_Iio`：bddAbove_Iio : BddAbove (Iio a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem powerlt_le {a b c : Cardinal.{u}} : a ^< b ≤ c ↔ ∀ x < b, a ^ x ≤ c := by
  rw [powerlt, ciSup_le_iff']
  · simp
  · rw [← image_eq_range]
    exact bddAbove_image.{u, u} _ bddAbove_Iio
/-
**Cardinal.powerlt_le_powerlt_left** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：powerlt_le_powerlt_left {a b c : Cardinal} (h : b <= c) : a ^< b <= a ^< c
参数：h : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.powerlt_le`：powerlt_le {a b c : Cardinal.{u}} : a ^< b <= c ↔ f
orall x < b, a ^ x <= c
· 使用定理 `Cardinal.le_powerlt`：le_powerlt {b c : Cardinal.{u}} (a) (h : c < b) : (
a ^ c) <= a ^< b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem powerlt_le_powerlt_left {a b c : Cardinal} (h : b ≤ c) : a ^< b ≤ a ^< c :=
  powerlt_le.2 fun _ hx => le_powerlt a <| hx.trans_le h
/-
**Cardinal.powerlt_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：powerlt_mono_left (a) : Monotone fun c => a ^< c
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.powerlt_le_powerlt_left`：powerlt_le_powerlt_left {a b c : Cardi
nal} (h : b <= c) : a ^< b <= a ^< c
-/
theorem powerlt_mono_left (a) : Monotone fun c => a ^< c := fun _ _ => powerlt_le_powerlt_left
/-
**Cardinal.powerlt_succ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：powerlt_succ {a b : Cardinal} (h : a != 0) : a ^< succ b = a ^ b
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.powerlt_le`：powerlt_le {a b c : Cardinal.{u}} : a ^< b <= c ↔ f
orall x < b, a ^ x <= c
· 使用定理 `Cardinal.power_le_power_left`：power_le_power_left : forall {a b c : Card
inal}, a != 0 -> b <= c -> a ^ b <= a ^ c
· 使用定理 `Order.le_of_lt_succ`：le_of_lt_succ {a b : α} : a < succ b -> a <= b
· 使用定理 `Cardinal.le_powerlt`：le_powerlt {b c : Cardinal.{u}} (a) (h : c < b) : (
a ^ c) <= a ^< b
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
-/
theorem powerlt_succ {a b : Cardinal} (h : a ≠ 0) : a ^< succ b = a ^ b :=
  (powerlt_le.2 fun _ h' => power_le_power_left h <| le_of_lt_succ h').antisymm <|
    le_powerlt a (lt_succ b)
/-
**Cardinal.powerlt_min** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：powerlt_min {a b c : Cardinal} : a ^< min b c = min (a ^< b) (a ^< c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `Cardinal.powerlt_mono_left`：powerlt_mono_left (a) : Monotone fun c => a 
^< c
-/
theorem powerlt_min {a b c : Cardinal} : a ^< min b c = min (a ^< b) (a ^< c) :=
  (powerlt_mono_left a).map_min
/-
**Cardinal.powerlt_max** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：powerlt_max {a b c : Cardinal} : a ^< max b c = max (a ^< b) (a ^< c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `Cardinal.powerlt_mono_left`：powerlt_mono_left (a) : Monotone fun c => a 
^< c
-/
theorem powerlt_max {a b c : Cardinal} : a ^< max b c = max (a ^< b) (a ^< c) :=
  (powerlt_mono_left a).map_max
/-
**Cardinal.zero_powerlt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：zero_powerlt {a : Cardinal} (h : a != 0) : 0 ^< a = 1
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.powerlt_le`：powerlt_le {a b c : Cardinal.{u}} : a ^< b <= c ↔ f
orall x < b, a ^ x <= c
· 使用定理 `Cardinal.zero_power_le`：zero_power_le (c : Cardinal.{u}) : (0 : Cardinal
.{u}) ^ c <= 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.power_zero`：power_zero (a : Cardinal) : a ^ (0 : Cardinal) = 1
· 使用定理 `Cardinal.le_powerlt`：le_powerlt {b c : Cardinal.{u}} (a) (h : c < b) : (
a ^ c) <= a ^< b
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem zero_powerlt {a : Cardinal} (h : a ≠ 0) : 0 ^< a = 1 := by
  apply (powerlt_le.2 fun c _ => zero_power_le _).antisymm
  rw [← power_zero]
  exact le_powerlt 0 (pos_iff_ne_zero.2 h)

@[simp]
/-
**Cardinal.powerlt_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：powerlt_zero {a : Cardinal} : a ^< 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.iSup_of_empty`：∀ {ι : Sort u_1} (f : ι → Cardinal.{u_2}) [IsEmp
ty ι], iSup f = 0
· 使用定理 `Subtype.isEmpty_of_false`：Subtype.isEmpty_of_false {p : α -> Prop} (hp :
 forall a, ¬p a) : IsEmpty (Subtype p)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用定理 `not_lt_zero`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], ¬a < 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem powerlt_zero {a : Cardinal} : a ^< 0 = 0 := by
  convert! Cardinal.iSup_of_empty _
  exact Subtype.isEmpty_of_false fun x => mem_Iio.not.mpr not_lt_zero

/-- The cardinality of a set is an upper-bound for the amount of elements before the set's mex
(minimum excluded value) -/
/-
**Cardinal._root_.WellFounded.cardinalMk_subtype_lt_min_compl_le** 是 Mathlib 中的一
个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cardinality of a set is an upper-bound for the amount of elements before the
 set's mex
(minimum excluded value)
-/
theorem _root_.WellFounded.cardinalMk_subtype_lt_min_compl_le {r : α → α → Prop}
    (wf : WellFounded r) {s : Set α} (hs : sᶜ.Nonempty) : #{ x // r x (wf.min sᶜ hs) } ≤ #s :=
  Cardinal.mk_le_mk_of_subset fun _ ↦ wf.mem_of_lt_min_compl

end Cardinal

