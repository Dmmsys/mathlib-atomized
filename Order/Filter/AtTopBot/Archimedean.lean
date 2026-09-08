/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Filter.AtTopBot.Group
public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.Tactic.GCongr
import Mathlib.Algebra.Order.Group.Basic

/-!
# `Filter.atTop` filter and archimedean (semi)rings/fields

In this file we prove that for a linear ordered archimedean semiring `R` and a function `f : α → ℕ`,
the function `Nat.cast ∘ f : α → R` tends to `Filter.atTop` along a filter `l` if and only if so
does `f`. We also prove that `Nat.cast : ℕ → R` tends to `Filter.atTop` along `Filter.atTop`, as
well as version of these two results for `ℤ` (and a ring `R`) and `ℚ` (and a field `R`).
-/

public section


variable {α R : Type*}

open Filter Set Function

@[simp]
/-
**Nat.comap_cast_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.comap_cast_atTop [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
 [Archimedean R] : comap ((↑) : Nat -> R) atTop = atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_embedding_atTop`：comap_embedding_atTop [Preorder β] [Preord
er γ] {e : β -> γ} (hm : forall b₁ b₂, e b₁ <= e b₂ ↔ b₁ <= b₂) (hu : forall c, 
exists b, c <= e b…
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `exists_nat_ge`：exists_nat_ge (x : R) : exists n : Nat, x <= n
-/
theorem Nat.comap_cast_atTop [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R] :
    comap ((↑) : ℕ → R) atTop = atTop :=
  comap_embedding_atTop (fun _ _ => Nat.cast_le) exists_nat_ge
/-
**tendsto_natCast_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_natCast_atTop_iff [Semiring R] [PartialOrder R] [IsStrictOrderedRi
ng R] [Archimedean R] {f : α -> Nat} {l : Filter α} : Tendsto (fun n => (f n : R
)) l atTop ↔ Tendsto f l atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_embedding`：tendsto_atTop_embedding [Preorder β] [Pr
eorder γ] {f : α -> β} {e : β -> γ} {l : Filter α} (hm : forall b₁ b₂, e b₁ <= e
 b₂ ↔ b₁ <= b₂) (hu …
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `exists_nat_ge`：exists_nat_ge (x : R) : exists n : Nat, x <= n
-/
theorem tendsto_natCast_atTop_iff [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R] {f : α → ℕ}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atTop ↔ Tendsto f l atTop :=
  tendsto_atTop_embedding (fun _ _ => Nat.cast_le) exists_nat_ge
/-
**PNat.tendsto_comp_val_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PNat.tendsto_comp_val_iff {β : Type*} {f : Nat -> β} {l : Filter β} : Tend
sto (fun x : Nat+ => f x) atTop l ↔ Tendsto f atTop l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_comp_val_Ioi_atTop`：tendsto_comp_val_Ioi_atTop [Preorder 
α] [IsDirectedOrder α] [NoMaxOrder α] {a : α} {f : α -> β} {l : Filter β} : Tend
sto (fun x : Ioi a => f…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
-/
theorem PNat.tendsto_comp_val_iff {β : Type*} {f : ℕ → β} {l : Filter β} :
    Tendsto (fun x : ℕ+ => f x) atTop l ↔ Tendsto f atTop l := by
  exact tendsto_comp_val_Ioi_atTop
/-
**tendsto_natCast_atTop_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_natCast_atTop_atTop [Semiring R] [PartialOrder R] [IsOrderedRing R
] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_atTop_atTop`：∀ {α : Type u_3} {β : Type u_4} [inst : Pr
eorder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → (∀ (b : β), ∃ a, b ≤
 f a) → Filter.Ten…
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `exists_nat_ge`：exists_nat_ge (x : R) : exists n : Nat, x <= n
-/
theorem tendsto_natCast_atTop_atTop [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] :
    Tendsto ((↑) : ℕ → R) atTop atTop :=
  Nat.mono_cast.tendsto_atTop_atTop exists_nat_ge
/-
**tendsto_PNat_val_atTop_atTop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_PNat_val_atTop_atTop : Tendsto PNat.val atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_atTop_of_monotone`：tendsto_atTop_atTop_of_monotone 
[Preorder α] [Preorder β] {f : α -> β} (hf : Monotone f) (h : forall b, exists a
, b <= f a) : Tendsto f atTo…
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
lemma tendsto_PNat_val_atTop_atTop : Tendsto PNat.val atTop atTop :=
  tendsto_atTop_atTop_of_monotone (fun _ _ h ↦ h) fun a ↦ ⟨Nat.succPNat a, Nat.le_succ a⟩
/-
**Filter.Eventually.natCast_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.natCast_atTop [Semiring R] [PartialOrder R] [IsOrderedRi
ng R] [Archimedean R] {p : R -> Prop} (h : forallᶠ (x : R) in atTop, p x) : fora
llᶠ (n : Nat) in atTop, p n
参数：h : forallᶠ (x : R) in atTop, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
-/
theorem Filter.Eventually.natCast_atTop [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] {p : R → Prop}
    (h : ∀ᶠ (x : R) in atTop, p x) : ∀ᶠ (n : ℕ) in atTop, p n :=
  tendsto_natCast_atTop_atTop.eventually h
/-
**Int.comap_cast_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {R : Type u_2} [inst : Ring R] [inst_1 : PartialOrder R] [IsStrictOrdere
dRing R] [Archimedean R],   Filter.comap Int.cast Filter.atTop = Filter.atTop
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_embedding_atTop`：comap_embedding_atTop [Preorder β] [Preord
er γ] {e : β -> γ} (hm : forall b₁ b₂, e b₁ <= e b₂ ↔ b₁ <= b₂) (hu : forall c, 
exists b, c <= e b…
· 使用定理 `Int.cast_le`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m ≤ ↑
n…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `exists_nat_ge`：exists_nat_ge (x : R) : exists n : Nat, x <= n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
-/
@[simp] theorem Int.comap_cast_atTop [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R] :
    comap ((↑) : ℤ → R) atTop = atTop :=
  comap_embedding_atTop (fun _ _ => Int.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge r; ⟨n, mod_cast hn⟩

@[simp]
/-
**Int.comap_cast_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.comap_cast_atBot [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [Ar
chimedean R] : comap ((↑) : Int -> R) atBot = atBot
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_embedding_atBot`：∀ {β : Type u_4} {γ : Type u_5} [inst : Pr
eorder β] [inst_1 : Preorder γ] {e : β → γ},   (∀ (b₁ b₂ : β), e b₂ ≤ e b₁ ↔ b₂ 
≤ b₁) → (∀ (c : γ)…
· 使用定理 `Int.cast_le`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m ≤ ↑
n…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `exists_nat_ge`：exists_nat_ge (x : R) : exists n : Nat, x <= n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem Int.comap_cast_atBot [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R] :
    comap ((↑) : ℤ → R) atBot = atBot :=
  comap_embedding_atBot (fun _ _ => Int.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge (-r)
    ⟨-n, by simpa [neg_le] using hn⟩
/-
**tendsto_intCast_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_intCast_atTop_iff [Ring R] [PartialOrder R] [IsStrictOrderedRing R
] [Archimedean R] {f : α -> Int} {l : Filter α} : Tendsto (fun n => (f n : R)) l
 atTop ↔ Tendsto f l atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.comap_cast_atTop`：∀ {R : Type u_2} [inst : Ring R] [inst_1 : Partial
Order R] [IsStrictOrderedRing R] [Archimedean R],   Filter.comap Int.cast Filter
.atTop = F…
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_intCast_atTop_iff [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R]
    {f : α → ℤ}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atTop ↔ Tendsto f l atTop := by
  rw [← @Int.comap_cast_atTop R, tendsto_comap_iff]; rfl
/-
**tendsto_intCast_atBot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_intCast_atBot_iff [Ring R] [PartialOrder R] [IsStrictOrderedRing R
] [Archimedean R] {f : α -> Int} {l : Filter α} : Tendsto (fun n => (f n : R)) l
 atBot ↔ Tendsto f l atBot
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.comap_cast_atBot`：Int.comap_cast_atBot [Ring R] [PartialOrder R] [Is
StrictOrderedRing R] [Archimedean R] : comap ((↑) : Int -> R) atBot = atBot
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_intCast_atBot_iff [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R] {f : α → ℤ}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atBot ↔ Tendsto f l atBot := by
  rw [← @Int.comap_cast_atBot R, tendsto_comap_iff]; rfl
/-
**tendsto_intCast_atTop_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_intCast_atTop_atTop [Ring R] [PartialOrder R] [IsStrictOrderedRing
 R] [Archimedean R] : Tendsto ((↑) : Int -> R) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_intCast_atTop_iff`：tendsto_intCast_atTop_iff [Ring R] [PartialOr
der R] [IsStrictOrderedRing R] [Archimedean R] {f : α -> Int} {l : Filter α} : T
endsto (fun n =…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
theorem tendsto_intCast_atTop_atTop [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R] :
    Tendsto ((↑) : ℤ → R) atTop atTop :=
  tendsto_intCast_atTop_iff.2 tendsto_id
/-
**Filter.Eventually.intCast_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.intCast_atTop [Ring R] [PartialOrder R] [IsStrictOrdered
Ring R] [Archimedean R] {p : R -> Prop} (h : forallᶠ (x : R) in atTop, p x) : fo
rallᶠ (n : Int) in atTop, p n
参数：h : forallᶠ (x : R) in atTop, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.comap_cast_atTop`：∀ {R : Type u_2} [inst : Ring R] [inst_1 : Partial
Order R] [IsStrictOrderedRing R] [Archimedean R],   Filter.comap Int.cast Filter
.atTop = F…
· 使用定理 `Filter.Eventually.comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} 
{p : β → Prop},   (∀ᶠ (b : β) in g, p b) → ∀ (f : α → β), ∀ᶠ (a : α) in Filter.c
omap f g, p (…
-/
theorem Filter.Eventually.intCast_atTop [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R] {p : R → Prop}
    (h : ∀ᶠ (x : R) in atTop, p x) : ∀ᶠ (n : ℤ) in atTop, p n := by
  rw [← Int.comap_cast_atTop (R := R)]; exact h.comap _
/-
**Filter.Eventually.intCast_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.intCast_atBot [Ring R] [PartialOrder R] [IsStrictOrdered
Ring R] [Archimedean R] {p : R -> Prop} (h : forallᶠ (x : R) in atBot, p x) : fo
rallᶠ (n : Int) in atBot, p n
参数：h : forallᶠ (x : R) in atBot, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.comap_cast_atBot`：Int.comap_cast_atBot [Ring R] [PartialOrder R] [Is
StrictOrderedRing R] [Archimedean R] : comap ((↑) : Int -> R) atBot = atBot
· 使用定理 `Filter.Eventually.comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} 
{p : β → Prop},   (∀ᶠ (b : β) in g, p b) → ∀ (f : α → β), ∀ᶠ (a : α) in Filter.c
omap f g, p (…
-/
theorem Filter.Eventually.intCast_atBot [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R] {p : R → Prop}
    (h : ∀ᶠ (x : R) in atBot, p x) : ∀ᶠ (n : ℤ) in atBot, p n := by
  rw [← Int.comap_cast_atBot (R := R)]; exact h.comap _

@[simp]
/-
**Rat.comap_cast_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Rat.comap_cast_atTop [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Ar
chimedean R] : comap ((↑) : Rat -> R) atTop = atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_embedding_atTop`：comap_embedding_atTop [Preorder β] [Preord
er γ] {e : β -> γ} (hm : forall b₁ b₂, e b₁ <= e b₂ ↔ b₁ <= b₂) (hu : forall c, 
exists b, c <= e b…
· 使用定理 `Rat.cast_le`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p ≤ ↑q ↔ p ≤ q
· 使用定理 `exists_nat_ge`：exists_nat_ge (x : R) : exists n : Nat, x <= n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
-/
theorem Rat.comap_cast_atTop [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R] :
    comap ((↑) : ℚ → R) atTop = atTop :=
  comap_embedding_atTop (fun _ _ => Rat.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge r; ⟨n, by simpa⟩
/-
**Rat.comap_cast_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {R : Type u_2} [inst : Field R] [inst_1 : LinearOrder R] [IsStrictOrdere
dRing R] [Archimedean R],   Filter.comap Rat.cast Filter.atBot = Filter.atBot
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_embedding_atBot`：∀ {β : Type u_4} {γ : Type u_5} [inst : Pr
eorder β] [inst_1 : Preorder γ] {e : β → γ},   (∀ (b₁ b₂ : β), e b₂ ≤ e b₁ ↔ b₂ 
≤ b₁) → (∀ (c : γ)…
· 使用定理 `Rat.cast_le`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p ≤ ↑q ↔ p ≤ q
· 使用定理 `exists_nat_ge`：exists_nat_ge (x : R) : exists n : Nat, x <= n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
@[simp] theorem Rat.comap_cast_atBot [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Archimedean R] :
    comap ((↑) : ℚ → R) atBot = atBot :=
  comap_embedding_atBot (fun _ _ => Rat.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge (-r)
    ⟨-n, by simpa [neg_le]⟩
/-
**tendsto_ratCast_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_ratCast_atTop_iff [Field R] [LinearOrder R] [IsStrictOrderedRing R
] [Archimedean R] {f : α -> Rat} {l : Filter α} : Tendsto (fun n => (f n : R)) l
 atTop ↔ Tendsto f l atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.comap_cast_atTop`：Rat.comap_cast_atTop [Field R] [LinearOrder R] [Is
StrictOrderedRing R] [Archimedean R] : comap ((↑) : Rat -> R) atTop = atTop
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_ratCast_atTop_iff [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R]
    {f : α → ℚ}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atTop ↔ Tendsto f l atTop := by
  rw [← @Rat.comap_cast_atTop R, tendsto_comap_iff]; rfl
/-
**tendsto_ratCast_atBot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_ratCast_atBot_iff [Field R] [LinearOrder R] [IsStrictOrderedRing R
] [Archimedean R] {f : α -> Rat} {l : Filter α} : Tendsto (fun n => (f n : R)) l
 atBot ↔ Tendsto f l atBot
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.comap_cast_atBot`：∀ {R : Type u_2} [inst : Field R] [inst_1 : Linear
Order R] [IsStrictOrderedRing R] [Archimedean R],   Filter.comap Rat.cast Filter
.atBot = F…
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_ratCast_atBot_iff [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Archimedean R] {f : α → ℚ}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atBot ↔ Tendsto f l atBot := by
  rw [← @Rat.comap_cast_atBot R, tendsto_comap_iff]; rfl
/-
**Filter.Eventually.ratCast_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.ratCast_atTop [Field R] [LinearOrder R] [IsStrictOrdered
Ring R] [Archimedean R] {p : R -> Prop} (h : forallᶠ (x : R) in atTop, p x) : fo
rallᶠ (n : Rat) in atTop, p n
参数：h : forallᶠ (x : R) in atTop, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.comap_cast_atTop`：Rat.comap_cast_atTop [Field R] [LinearOrder R] [Is
StrictOrderedRing R] [Archimedean R] : comap ((↑) : Rat -> R) atTop = atTop
· 使用定理 `Filter.Eventually.comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} 
{p : β → Prop},   (∀ᶠ (b : β) in g, p b) → ∀ (f : α → β), ∀ᶠ (a : α) in Filter.c
omap f g, p (…
-/
theorem Filter.Eventually.ratCast_atTop [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Archimedean R] {p : R → Prop}
    (h : ∀ᶠ (x : R) in atTop, p x) : ∀ᶠ (n : ℚ) in atTop, p n := by
  rw [← Rat.comap_cast_atTop (R := R)]; exact h.comap _
/-
**Filter.Eventually.ratCast_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.ratCast_atBot [Field R] [LinearOrder R] [IsStrictOrdered
Ring R] [Archimedean R] {p : R -> Prop} (h : forallᶠ (x : R) in atBot, p x) : fo
rallᶠ (n : Rat) in atBot, p n
参数：h : forallᶠ (x : R) in atBot, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.comap_cast_atBot`：∀ {R : Type u_2} [inst : Field R] [inst_1 : Linear
Order R] [IsStrictOrderedRing R] [Archimedean R],   Filter.comap Rat.cast Filter
.atBot = F…
· 使用定理 `Filter.Eventually.comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} 
{p : β → Prop},   (∀ᶠ (b : β) in g, p b) → ∀ (f : α → β), ∀ᶠ (a : α) in Filter.c
omap f g, p (…
-/
theorem Filter.Eventually.ratCast_atBot [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Archimedean R] {p : R → Prop}
    (h : ∀ᶠ (x : R) in atBot, p x) : ∀ᶠ (n : ℚ) in atBot, p n := by
  rw [← Rat.comap_cast_atBot (R := R)]; exact h.comap _
/-
**atTop_hasAntitoneBasis_of_archimedean** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：atTop_hasAntitoneBasis_of_archimedean [Semiring R] [PartialOrder R] [IsOrd
eredRing R] [Archimedean R] : (atTop : Filter R).HasAntitoneBasis fun n : Nat =>
 Ici n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasAntitoneBasis.comp_mono`：∀ {ι : Type u_1} {ι' : Type u_2} {α :
 Type u_3} [Nonempty ι] [inst : Preorder ι] [IsDirectedOrder ι]   [inst_2 : Preo
rder ι'] {l : Filter α}…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `Filter.hasAntitoneBasis_atTop`：hasAntitoneBasis_atTop [Nonempty α] : (@a
tTop α _).HasAntitoneBasis Ici
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
-/
theorem atTop_hasAntitoneBasis_of_archimedean [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] :
    (atTop : Filter R).HasAntitoneBasis fun n : ℕ => Ici n :=
  hasAntitoneBasis_atTop.comp_mono Nat.mono_cast tendsto_natCast_atTop_atTop
/-
**atTop_hasCountableBasis_of_archimedean** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：atTop_hasCountableBasis_of_archimedean [Semiring R] [PartialOrder R] [IsOr
deredRing R] [Archimedean R] : (atTop : Filter R).HasCountableBasis (fun _ : Nat
 => True) fun n => Ici n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasAntitoneBasis.toHasBasis`：∀ {α : Type u_1} {ι'' : Type u_6} [i
nst : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → l
.HasBasis (fun x => True…
· 使用定理 `atTop_hasAntitoneBasis_of_archimedean`：atTop_hasAntitoneBasis_of_archime
dean [Semiring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R] : (atTop : 
Filter R).HasAntitoneBasis …
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用定理 `instCountableNat`：Countable ℕ
-/
theorem atTop_hasCountableBasis_of_archimedean [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] :
    (atTop : Filter R).HasCountableBasis (fun _ : ℕ => True) fun n => Ici n :=
  ⟨atTop_hasAntitoneBasis_of_archimedean.1, to_countable _⟩
/-
**atBot_hasCountableBasis_of_archimedean** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：atBot_hasCountableBasis_of_archimedean [Ring R] [PartialOrder R] [IsOrdere
dRing R] [Archimedean R] : (atBot : Filter R).HasCountableBasis (fun _ : Int => 
True) fun m => Iic m where countable
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用引理 `Filter.atBot_basis`：atBot_basis {α : Type*} [Preorder α] [IsCodirectedOr
der α] [Nonempty α] : (@atBot α _).HasBasis (fun _ => True) Iic
· 使用定理 `instIsCodirectedOrder`：∀ {R : Type u_3} [inst : Ring R] [inst_1 : Partia
lOrder R] [IsOrderedRing R] [Archimedean R], IsCodirectedOrder R
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `exists_int_le`：exists_int_le (x : R) : exists n : Int, n <= x
· 使用定理 `trivial`：True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用定理 `instCountableInt`：Countable ℤ
-/
theorem atBot_hasCountableBasis_of_archimedean [Ring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] :
    (atBot : Filter R).HasCountableBasis (fun _ : ℤ => True) fun m => Iic m where
  countable := to_countable _
  toHasBasis :=
    atBot_basis.to_hasBasis
      (fun x _ => let ⟨m, hm⟩ := exists_int_le x; ⟨m, trivial, Iic_subset_Iic.2 hm⟩)
      fun m _ => ⟨m, trivial, Subset.rfl⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) atTop_isCountablyGenerated_of_archimedean
    [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] : (atTop : Filter R).IsCountablyGenerated :=
  atTop_hasCountableBasis_of_archimedean.isCountablyGenerated
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) atBot_isCountablyGenerated_of_archimedean
    [Ring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] : (atBot : Filter R).IsCountablyGenerated :=
  atBot_hasCountableBasis_of_archimedean.isCountablyGenerated

namespace Filter

variable {l : Filter α} {f : α → R} {r : R}

/-
**Filter.map_add_atTop_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_add_atTop_eq [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] 
[IsDirectedOrder α] (k : α) : map (fun a => a + k) atTop = atTop
参数：k : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_atTop_eq_of_gc`：map_atTop_eq_of_gc [Preorder α] [IsDirectedOr
der α] [PartialOrder β] [IsDirectedOrder β] {f : α -> β} (g : β -> α) (b : β) (h
f : Monotone f)…
· 使用定理 `add_left_mono`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [Ad
dRightMono α] {a : α}, Monotone fun x => x + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem map_add_atTop_eq [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
    [IsDirectedOrder α] (k : α) : map (fun a => a + k) atTop = atTop :=
  map_atTop_eq_of_gc (fun a => a - k) 0 add_left_mono (by simp [le_sub_iff_add_le]) (by simp)
/-
**Filter.map_sub_atTop_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_sub_atTop_eq [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] 
[IsDirectedOrder α] (k : α) : map (fun a => a - k) atTop = atTop
参数：k : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Filter.map_add_atTop_eq`：map_add_atTop_eq [AddCommGroup α] [PartialOrder
 α] [IsOrderedAddMonoid α] [IsDirectedOrder α] (k : α) : map (fun a => a + k) at
Top = atTop
-/
theorem map_sub_atTop_eq [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
    [IsDirectedOrder α] (k : α) : map (fun a => a - k) atTop = atTop := by
  simp_rw [sub_eq_add_neg]
  apply map_add_atTop_eq

section LinearOrderedSemiring

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R]

/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the left) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `Filter.Tendsto.const_mul_atTop`). -/
/-
**Filter.Tendsto.const_mul_atTop'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {R : Type u_2} {l : Filter α} {f : α → R} {r : R} [inst :
 Semiring R] [inst_1 : LinearOrder R]   [IsStrictOrderedRing R] [Archimedean R],
   0 < r → Filter.Tendsto f l Filter.atTop → Filter.Tendsto (fun x => r * f x) l
 Filter.atTop
参数：fun x => r * f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_atTop`：tendsto_atTop [Preorder β] {m : α -> β} {f : Filte
r α} : Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a
· 使用定理 `Archimedean.arch`：∀ {R : Type u_2} {inst : AddCommMonoid R} {inst_1 : Pa
rtialOrder R} [self : Archimedean R] (x : R) {y : R},   0 < y → ∃ n, x ≤ n • y
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `nsmul_eq_mul'`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (a : α) (n :
 ℕ), n • a = a * ↑n
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
· 使用引理 `Mathlib.Meta.Positivity.nonneg_of_isNat`：nonneg_of_isNat {n : Nat} [Semi
ring A] [PartialOrder A] [IsOrderedRing A] (h : NormNum.IsNat e n) : 0 <= (e : A
)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
If a function tends to infinity along a filter, then this function multiplied by
 a positive
constant (on the left) also tends to infinity. The archimedean assumption is con
venient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in o
rdered fields is
given in `Filter.Tendsto.const_mul_atTop`).
-/
theorem Tendsto.const_mul_atTop' (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atTop := by
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨n : ℕ, hn : 1 ≤ n • r⟩ := Archimedean.arch 1 hr
  rw [nsmul_eq_mul'] at hn
  filter_upwards [tendsto_atTop.1 hf (n * max b 0)] with x hx
  calc
    b ≤ 1 * max b 0 := by
    { rw [one_mul]
      exact le_max_left _ _ }
    _ ≤ r * n * max b 0 := by gcongr
    _ = r * (n * max b 0) := by rw [mul_assoc]
    _ ≤ r * f x := by gcongr

/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the right) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `Filter.Tendsto.atTop_mul_const`). -/
/-
**Filter.Tendsto.atTop_mul_const'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {R : Type u_2} {l : Filter α} {f : α → R} {r : R} [inst :
 Semiring R] [inst_1 : LinearOrder R]   [IsStrictOrderedRing R] [Archimedean R],
   0 < r → Filter.Tendsto f l Filter.atTop → Filter.Tendsto (fun x => f x * r) l
 Filter.atTop
参数：fun x => f x * r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_atTop`：tendsto_atTop [Preorder β] {m : α -> β} {f : Filte
r α} : Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a
· 使用定理 `Archimedean.arch`：∀ {R : Type u_2} {inst : AddCommMonoid R} {inst_1 : Pa
rtialOrder R} [self : Archimedean R] (x : R) {y : R},   0 < y → ∃ n, x ≤ n • y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
· 使用引理 `Mathlib.Meta.Positivity.nonneg_of_isNat`：nonneg_of_isNat {n : Nat} [Semi
ring A] [PartialOrder A] [IsOrderedRing A] (h : NormNum.IsNat e n) : 0 <= (e : A
)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
If a function tends to infinity along a filter, then this function multiplied by
 a positive
constant (on the right) also tends to infinity. The archimedean assumption is co
nvenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in o
rdered fields is
given in `Filter.Tendsto.atTop_mul_const`).
-/
theorem Tendsto.atTop_mul_const' (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atTop := by
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨n : ℕ, hn : 1 ≤ n • r⟩ := Archimedean.arch 1 hr
  have hn' : 1 ≤ (n : R) * r := by rwa [nsmul_eq_mul] at hn
  filter_upwards [tendsto_atTop.1 hf (max b 0 * n)] with x hx
  calc
    b ≤ max b 0 * 1 := by
    { rw [mul_one]
      exact le_max_left _ _ }
    _ ≤ max b 0 * (n * r) := by gcongr
    _ = max b 0 * n * r := by rw [mul_assoc]
    _ ≤ f x * r := by gcongr

end LinearOrderedSemiring

section LinearOrderedRing

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R]

/-- See also `Filter.Tendsto.atTop_mul_const_of_neg` for a version of this lemma for
linearly ordered fields which does not require the `Archimedean` assumption. -/
/-
**Filter.Tendsto.atTop_mul_const_of_neg'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tends
to`。
形式化陈述：∀ {α : Type u_1} {R : Type u_2} {l : Filter α} {f : α → R} {r : R} [inst :
 Ring R] [inst_1 : LinearOrder R]   [IsStrictOrderedRing R] [Archimedean R],   r
 < 0 → Filter.Tendsto f l Filter.atTop → Filter.Tendsto (fun x => f x * r) l Fil
ter.atBot
参数：fun x => f x * r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Filter.Tendsto.atTop_mul_const'`：∀ {α : Type u_1} {R : Type u_2} {l : Fi
lter α} {f : α → R} {r : R} [inst : Semiring R] [inst_1 : LinearOrder R]   [IsSt
rictOrderedRing R] [A…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
See also `Filter.Tendsto.atTop_mul_const_of_neg` for a version of this lemma for
linearly ordered fields which does not require the `Archimedean` assumption.
-/
theorem Tendsto.atTop_mul_const_of_neg' (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atBot := by
  simpa only [tendsto_neg_atTop_iff, mul_neg] using hf.atTop_mul_const' (neg_pos.mpr hr)

/-- See also `Filter.Tendsto.atBot_mul_const` for a version of this lemma for
linearly ordered fields which does not require the `Archimedean` assumption. -/
/-
**Filter.Tendsto.atBot_mul_const'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {R : Type u_2} {l : Filter α} {f : α → R} {r : R} [inst :
 Ring R] [inst_1 : LinearOrder R]   [IsStrictOrderedRing R] [Archimedean R],   0
 < r → Filter.Tendsto f l Filter.atBot → Filter.Tendsto (fun x => f x * r) l Fil
ter.atBot
参数：fun x => f x * r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Tendsto.atTop_mul_const'`：∀ {α : Type u_1} {R : Type u_2} {l : Fi
lter α} {f : α → R} {r : R} [inst : Semiring R] [inst_1 : LinearOrder R]   [IsSt
rictOrderedRing R] [A…

--- 原说明 ---
See also `Filter.Tendsto.atBot_mul_const` for a version of this lemma for
linearly ordered fields which does not require the `Archimedean` assumption.
-/
theorem Tendsto.atBot_mul_const' (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atBot := by
  simp only [← tendsto_neg_atTop_iff, ← neg_mul] at hf ⊢
  exact hf.atTop_mul_const' hr

/-- See also `Filter.Tendsto.atBot_mul_const_of_neg` for a version of this lemma for
linearly ordered fields which does not require the `Archimedean` assumption. -/
/-
**Filter.Tendsto.atBot_mul_const_of_neg'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tends
to`。
形式化陈述：∀ {α : Type u_1} {R : Type u_2} {l : Filter α} {f : α → R} {r : R} [inst :
 Ring R] [inst_1 : LinearOrder R]   [IsStrictOrderedRing R] [Archimedean R],   r
 < 0 → Filter.Tendsto f l Filter.atBot → Filter.Tendsto (fun x => f x * r) l Fil
ter.atTop
参数：fun x => f x * r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Filter.Tendsto.atBot_mul_const'`：∀ {α : Type u_1} {R : Type u_2} {l : Fi
lter α} {f : α → R} {r : R} [inst : Ring R] [inst_1 : LinearOrder R]   [IsStrict
OrderedRing R] [Archi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
See also `Filter.Tendsto.atBot_mul_const_of_neg` for a version of this lemma for
linearly ordered fields which does not require the `Archimedean` assumption.
-/
theorem Tendsto.atBot_mul_const_of_neg' (hr : r < 0) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atTop := by
  simpa only [mul_neg, tendsto_neg_atBot_iff] using hf.atBot_mul_const' (neg_pos.2 hr)

end LinearOrderedRing

section LinearOrderedCancelAddCommMonoid

variable [AddCommMonoid R] [LinearOrder R] [IsOrderedCancelAddMonoid R] [Archimedean R]

/-
**Filter.Tendsto.atTop_nsmul_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {R : Type u_2} {l : Filter α} {r : R} [inst : AddCommMono
id R] [inst_1 : LinearOrder R]   [IsOrderedCancelAddMonoid R] [Archimedean R] {f
 : α → ℕ},   0 < r → Filter.Tendsto f l Filter.atTop → Filter.Tendsto (fun x => 
f x • r) l Filter.atTop
参数：fun x => f x • r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_atTop`：tendsto_atTop [Preorder β] {m : α -> β} {f : Filte
r α} : Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a
· 使用定理 `Archimedean.arch`：∀ {R : Type u_2} {inst : AddCommMonoid R} {inst_1 : Pa
rtialOrder R} [self : Archimedean R] (x : R) {y : R},   0 < y → ∃ n, x ≤ n • y
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `nsmul_le_nsmul_left`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Pre
order M] [AddLeftMono M] {a : M} {n m : ℕ},   0 ≤ a → n ≤ m → n • a ≤ m • a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Tendsto.atTop_nsmul_const {f : α → ℕ} (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • r) l atTop := by
  refine tendsto_atTop.mpr fun s => ?_
  obtain ⟨n : ℕ, hn : s ≤ n • r⟩ := Archimedean.arch s hr
  exact (tendsto_atTop.mp hf n).mono fun a ha => hn.trans (nsmul_le_nsmul_left hr.le ha)

end LinearOrderedCancelAddCommMonoid

section LinearOrderedAddCommGroup

variable [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R] [Archimedean R]

/-
**Filter.Tendsto.atTop_nsmul_neg_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto
`。
形式化陈述：∀ {α : Type u_1} {R : Type u_2} {l : Filter α} {r : R} [inst : AddCommGrou
p R] [inst_1 : LinearOrder R]   [IsOrderedAddMonoid R] [Archimedean R] {f : α → 
ℕ},   r < 0 → Filter.Tendsto f l Filter.atTop → Filter.Tendsto (fun x => f x • r
) l Filter.atBot
参数：fun x => f x • r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_nsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℕ)
, n • -a = -(n • a)
· 使用定理 `Filter.Tendsto.atTop_nsmul_const`：∀ {α : Type u_1} {R : Type u_2} {l : F
ilter α} {r : R} [inst : AddCommMonoid R] [inst_1 : LinearOrder R]   [IsOrderedC
ancelAddMonoid R] [Arc…
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem Tendsto.atTop_nsmul_neg_const {f : α → ℕ} (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • r) l atBot := by simpa using hf.atTop_nsmul_const (neg_pos.2 hr)
/-
**Filter.Tendsto.atTop_zsmul_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {R : Type u_2} {l : Filter α} {r : R} [inst : AddCommGrou
p R] [inst_1 : LinearOrder R]   [IsOrderedAddMonoid R] [Archimedean R] {f : α → 
ℤ},   0 < r → Filter.Tendsto f l Filter.atTop → Filter.Tendsto (fun x => f x • r
) l Filter.atTop
参数：fun x => f x • r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_atTop`：tendsto_atTop [Preorder β] {m : α -> β} {f : Filte
r α} : Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a
· 使用定理 `Archimedean.arch`：∀ {R : Type u_2} {inst : AddCommMonoid R} {inst_1 : Pa
rtialOrder R} [self : Archimedean R] (x : R) {y : R},   0 < y → ∃ n, x ≤ n • y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zsmul_le_zsmul_left`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
PartialOrder α] [IsOrderedAddMonoid α] {m n : ℤ} {a : α},   0 ≤ a → m ≤ n → m • 
a ≤ n • a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Tendsto.atTop_zsmul_const {f : α → ℤ} (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • r) l atTop := by
  refine tendsto_atTop.mpr fun s => ?_
  obtain ⟨n : ℕ, hn : s ≤ n • r⟩ := Archimedean.arch s hr
  replace hn : s ≤ (n : ℤ) • r := by simpa
  exact (tendsto_atTop.mp hf n).mono fun a ha => hn.trans (zsmul_le_zsmul_left hr.le ha)
/-
**Filter.Tendsto.atTop_zsmul_neg_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto
`。
形式化陈述：∀ {α : Type u_1} {R : Type u_2} {l : Filter α} {r : R} [inst : AddCommGrou
p R] [inst_1 : LinearOrder R]   [IsOrderedAddMonoid R] [Archimedean R] {f : α → 
ℤ},   r < 0 → Filter.Tendsto f l Filter.atTop → Filter.Tendsto (fun x => f x • r
) l Filter.atBot
参数：fun x => f x • r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zsmul_neg'`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ
), n • -a = -n • a
· 使用定理 `neg_zsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ)
, -n • a = -(n • a)
· 使用定理 `Filter.Tendsto.atTop_zsmul_const`：∀ {α : Type u_1} {R : Type u_2} {l : F
ilter α} {r : R} [inst : AddCommGroup R] [inst_1 : LinearOrder R]   [IsOrderedAd
dMonoid R] [Archimedea…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem Tendsto.atTop_zsmul_neg_const {f : α → ℤ} (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • r) l atBot := by simpa using hf.atTop_zsmul_const (neg_pos.2 hr)
/-
**Filter.Tendsto.atBot_zsmul_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {R : Type u_2} {l : Filter α} {r : R} [inst : AddCommGrou
p R] [inst_1 : LinearOrder R]   [IsOrderedAddMonoid R] [Archimedean R] {f : α → 
ℤ},   0 < r → Filter.Tendsto f l Filter.atBot → Filter.Tendsto (fun x => f x • r
) l Filter.atBot
参数：fun x => f x • r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Tendsto.atTop_zsmul_const`：∀ {α : Type u_1} {R : Type u_2} {l : F
ilter α} {r : R} [inst : AddCommGroup R] [inst_1 : LinearOrder R]   [IsOrderedAd
dMonoid R] [Archimedea…
-/
theorem Tendsto.atBot_zsmul_const {f : α → ℤ} (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x • r) l atBot := by
  simp only [← tendsto_neg_atTop_iff, ← neg_zsmul] at hf ⊢
  exact hf.atTop_zsmul_const hr
/-
**Filter.Tendsto.atBot_zsmul_neg_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto
`。
形式化陈述：∀ {α : Type u_1} {R : Type u_2} {l : Filter α} {r : R} [inst : AddCommGrou
p R] [inst_1 : LinearOrder R]   [IsOrderedAddMonoid R] [Archimedean R] {f : α → 
ℤ},   r < 0 → Filter.Tendsto f l Filter.atBot → Filter.Tendsto (fun x => f x • r
) l Filter.atTop
参数：fun x => f x • r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zsmul_neg'`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ
), n • -a = -n • a
· 使用定理 `neg_zsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ)
, -n • a = -(n • a)
· 使用定理 `Filter.Tendsto.atBot_zsmul_const`：∀ {α : Type u_1} {R : Type u_2} {l : F
ilter α} {r : R} [inst : AddCommGroup R] [inst_1 : LinearOrder R]   [IsOrderedAd
dMonoid R] [Archimedea…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem Tendsto.atBot_zsmul_neg_const {f : α → ℤ} (hr : r < 0) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x • r) l atTop := by simpa using hf.atBot_zsmul_const (neg_pos.2 hr)

end LinearOrderedAddCommGroup

end Filter

