/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Asymptotics.Theta

/-!
# Asymptotic equivalence

In this file, we prove properties of the relation `IsEquivalent l u v`,
which means that `u-v` is little o of `v` along the filter `l`.

Unlike `Is(Little|Big)O` relations, this one requires `u` and `v` to have the same codomain `β`.

## Notation

We use the notation `u ~[l] v := IsEquivalent l u v`, which you can use by opening the
`Asymptotics` locale.

## Main results

If `β` is a `NormedAddCommGroup` :

- `_ ~[l] _` is an equivalence relation
- Equivalent statements for `u ~[l] const _ c` :
  - If `c ≠ 0`, this is true iff `Tendsto u l (𝓝 c)` (see `isEquivalent_const_iff_tendsto`)
  - For `c = 0`, this is true iff `u =ᶠ[l] 0` (see `isEquivalent_zero_iff_eventually_zero`)

If `β` is a `NormedField` :

- Alternative characterization of the relation (see `isEquivalent_iff_exists_eq_mul`) :

  `u ~[l] v ↔ ∃ (φ : α → β) (hφ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v`

- Provided some non-vanishing hypothesis, this can be seen as `u ~[l] v ↔ Tendsto (u/v) l (𝓝 1)`
  (see `isEquivalent_iff_tendsto_one`)
- For any constant `c`, `u ~[l] v` implies `Tendsto u l (𝓝 c) ↔ Tendsto v l (𝓝 c)`
  (see `IsEquivalent.tendsto_nhds_iff`)
- `*` and `/` are compatible with `_ ~[l] _` (see `IsEquivalent.mul` and `IsEquivalent.div`)

If `β` is a `NormedLinearOrderedField` :

- If `u ~[l] v`, we have `Tendsto u l atTop ↔ Tendsto v l atTop`
  (see `IsEquivalent.tendsto_atTop_iff`)

## Implementation Notes

Note that `IsEquivalent` takes the parameters `(l : Filter α) (u v : α → β)` in that order.
This is to enable `calc` support, as `calc` requires that the last two explicit arguments are `u v`.

-/

public section


namespace Asymptotics

open Filter Function

open Topology

section NormedAddCommGroup

variable {α β : Type*} [NormedAddCommGroup β]

variable {u v w : α → β} {l : Filter α}

/-
**Asymptotics.IsEquivalent.isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsEq
uivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u v : α → β
} {l : Filter α},   Asymptotics.IsEquivalent l u v → (u - v) =o[l] v
参数：u - v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsEquivalent.isLittleO (h : u ~[l] v) : (u - v) =o[l] v := h

nonrec theorem IsEquivalent.isBigO (h : u ~[l] v) : u =O[l] v :=
  (IsBigO.congr_of_sub h.isBigO.symm).mp (isBigO_refl _ _)
/-
**Asymptotics.IsEquivalent.isBigO_symm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.Is
Equivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u v : α → β
} {l : Filter α},   Asymptotics.IsEquivalent l u v → v =O[l] u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsLittleO.right_isBigO_add`：∀ {α : Type u_1} {E' : Type u_6}
 [inst : SeminormedAddCommGroup E'] {l : Filter α} {f₁ f₂ : α → E'},   f₁ =o[l] 
f₂ → f₂ =O[l] fun x => f₁ x …
· 使用定理 `Asymptotics.IsEquivalent.isLittleO`：∀ {α : Type u_1} {β : Type u_2} [ins
t : NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivale
nt l u v → (u - v) =o[l]…
-/
theorem IsEquivalent.isBigO_symm (h : u ~[l] v) : v =O[l] u := by
  convert! h.isLittleO.right_isBigO_add
  simp
/-
**Asymptotics.IsEquivalent.isTheta** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsEqui
valent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u v : α → β
} {l : Filter α},   Asymptotics.IsEquivalent l u v → u =Θ[l] v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.isBigO`：∀ {α : Type u_1} {β : Type u_2} [inst :
 NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent 
l u v → u =O[l] v
· 使用定理 `Asymptotics.IsEquivalent.isBigO_symm`：∀ {α : Type u_1} {β : Type u_2} [i
nst : NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquiva
lent l u v → v =O[l] u
-/
theorem IsEquivalent.isTheta (h : u ~[l] v) : u =Θ[l] v :=
  ⟨h.isBigO, h.isBigO_symm⟩
/-
**Asymptotics.IsEquivalent.isTheta_symm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.I
sEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u v : α → β
} {l : Filter α},   Asymptotics.IsEquivalent l u v → v =Θ[l] u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.isBigO_symm`：∀ {α : Type u_1} {β : Type u_2} [i
nst : NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquiva
lent l u v → v =O[l] u
· 使用定理 `Asymptotics.IsEquivalent.isBigO`：∀ {α : Type u_1} {β : Type u_2} [inst :
 NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent 
l u v → u =O[l] v
-/
theorem IsEquivalent.isTheta_symm (h : u ~[l] v) : v =Θ[l] u :=
  ⟨h.isBigO_symm, h.isBigO⟩

@[refl]
/-
**Asymptotics.IsEquivalent.refl** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsEquival
ent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u : α → β} 
{l : Filter α}, Asymptotics.IsEquivalent l u u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsEquivalent.eq_1`：∀ {α : Type u_1} {E' : Type u_6} [inst : 
SeminormedAddCommGroup E'] (l : Filter α) (u v : α → E'),   Asymptotics.IsEquiva
lent l u v = (u - v…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Asymptotics.isLittleO_zero`：isLittleO_zero : (fun _x => (0 : E')) =o[l] 
g'
-/
theorem IsEquivalent.refl : u ~[l] u := by
  rw [IsEquivalent, sub_self]
  exact isLittleO_zero _ _

@[symm]
/-
**Asymptotics.IsEquivalent.symm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsEquival
ent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u v : α → β
} {l : Filter α},   Asymptotics.IsEquivalent l u v → Asymptotics.IsEquivalent l 
v u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.symm`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u
_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filt
er α} {f₁ f₂ : α…
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
· 使用定理 `Asymptotics.IsEquivalent.isLittleO`：∀ {α : Type u_1} {β : Type u_2} [ins
t : NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivale
nt l u v → (u - v) =o[l]…
· 使用定理 `Asymptotics.IsEquivalent.isBigO_symm`：∀ {α : Type u_1} {β : Type u_2} [i
nst : NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquiva
lent l u v → v =O[l] u
-/
theorem IsEquivalent.symm (h : u ~[l] v) : v ~[l] u :=
  (h.isLittleO.trans_isBigO h.isBigO_symm).symm

@[trans]
/-
**Asymptotics.IsEquivalent.trans** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsEquiva
lent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {l : Filter 
α} {u v w : α → β},   Asymptotics.IsEquivalent l u v → Asymptotics.IsEquivalent 
l v w → Asymptotics.IsEquivalent l u w
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.triangle`：∀ {α : Type u_1} {F : Type u_4} {E' : Ty
pe u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : 
Filter α} {f₁ f₂ f₃ …
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
· 使用定理 `Asymptotics.IsEquivalent.isLittleO`：∀ {α : Type u_1} {β : Type u_2} [ins
t : NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivale
nt l u v → (u - v) =o[l]…
· 使用定理 `Asymptotics.IsEquivalent.isBigO`：∀ {α : Type u_1} {β : Type u_2} [inst :
 NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent 
l u v → u =O[l] v
-/
theorem IsEquivalent.trans {l : Filter α} {u v w : α → β} (huv : u ~[l] v) (hvw : v ~[l] w) :
    u ~[l] w :=
  (huv.isLittleO.trans_isBigO hvw.isBigO).triangle hvw.isLittleO
/-
**Asymptotics.IsEquivalent.congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsE
quivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u v w : α →
 β} {l : Filter α},   Asymptotics.IsEquivalent l u v → u =ᶠ[l] w → Asymptotics.I
sEquivalent l w v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ :
 α → F}, f₁ =o[l] …
· 使用定理 `Filter.EventuallyEq.sub`：∀ {α : Type u} {β : Type v} [inst : Sub β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f - f' =ᶠ[l] g - g'
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
theorem IsEquivalent.congr_left {u v w : α → β} {l : Filter α} (huv : u ~[l] v) (huw : u =ᶠ[l] w) :
    w ~[l] v :=
  huv.congr' (huw.sub (EventuallyEq.refl _ _)) (EventuallyEq.refl _ _)
/-
**Asymptotics.IsEquivalent.congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.Is
Equivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u v w : α →
 β} {l : Filter α},   Asymptotics.IsEquivalent l u v → v =ᶠ[l] w → Asymptotics.I
sEquivalent l u w
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
· 使用定理 `Asymptotics.IsEquivalent.congr_left`：∀ {α : Type u_1} {β : Type u_2} [in
st : NormedAddCommGroup β] {u v w : α → β} {l : Filter α},   Asymptotics.IsEquiv
alent l u v → u =ᶠ[l] w →…
-/
theorem IsEquivalent.congr_right {u v w : α → β} {l : Filter α} (huv : u ~[l] v) (hvw : v =ᶠ[l] w) :
    u ~[l] w :=
  (huv.symm.congr_left hvw).symm
/-
**Asymptotics.isEquivalent_zero_iff_eventually_zero** 是 Mathlib 中的一个定理，位于命名空间 `A
symptotics`。
形式化陈述：isEquivalent_zero_iff_eventually_zero : u ~[l] 0 ↔ u =ᶠ[l] 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsEquivalent.eq_1`：∀ {α : Type u_1} {E' : Type u_6} [inst : 
SeminormedAddCommGroup E'] (l : Filter α) (u v : α → E'),   Asymptotics.IsEquiva
lent l u v = (u - v…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Asymptotics.isLittleO_zero_right_iff`：isLittleO_zero_right_iff : (f'' =o
[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0
-/
theorem isEquivalent_zero_iff_eventually_zero : u ~[l] 0 ↔ u =ᶠ[l] 0 := by
  rw [IsEquivalent, sub_zero]
  exact isLittleO_zero_right_iff
/-
**Asymptotics.isEquivalent_zero_iff_isBigO_zero** 是 Mathlib 中的一个定理，位于命名空间 `Asymp
totics`。
形式化陈述：isEquivalent_zero_iff_isBigO_zero : u ~[l] 0 ↔ u =O[l] (0 : α -> β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.isBigO`：∀ {α : Type u_1} {β : Type u_2} [inst :
 NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent 
l u v → u =O[l] v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isEquivalent_zero_iff_eventually_zero`：isEquivalent_zero_iff
_eventually_zero : u ~[l] 0 ↔ u =ᶠ[l] 0
· 使用定理 `Filter.eventuallyEq_iff_exists_mem`：eventuallyEq_iff_exists_mem {l : Fil
ter α} {f g : α -> β} : f =ᶠ[l] g ↔ exists s in l, EqOn f g s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isBigO_zero_right_iff`：isBigO_zero_right_iff : (f'' =O[l] fu
n _x => (0 : F')) ↔ f'' =ᶠ[l] 0
-/
theorem isEquivalent_zero_iff_isBigO_zero : u ~[l] 0 ↔ u =O[l] (0 : α → β) := by
  refine ⟨IsEquivalent.isBigO, fun h ↦ ?_⟩
  rw [isEquivalent_zero_iff_eventually_zero, eventuallyEq_iff_exists_mem]
  exact ⟨{ x : α | u x = 0 }, isBigO_zero_right_iff.mp h, fun x hx ↦ hx⟩
/-
**Asymptotics.isEquivalent_const_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics`。
形式化陈述：isEquivalent_const_iff_tendsto {c : β} (h : c != 0) : u ~[l] const _ c ↔ T
endsto u l (𝓝 c)
参数：h : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isLittleO_const_iff`：isLittleO_const_iff {c : F''} (hc : c !
= 0) : (f'' =o[l] fun _x => c) ↔ Tendsto f'' l (𝓝 0)
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem isEquivalent_const_iff_tendsto {c : β} (h : c ≠ 0) :
    u ~[l] const _ c ↔ Tendsto u l (𝓝 c) := by
  simp +unfoldPartialApp only [IsEquivalent, const, isLittleO_const_iff h]
  constructor <;> intro h
  · have := h.sub (tendsto_const_nhds (x := -c))
    simp only [Pi.sub_apply, sub_neg_eq_add, sub_add_cancel, zero_add] at this
    exact this
  · have := h.sub (tendsto_const_nhds (x := c))
    rwa [sub_self] at this
/-
**Asymptotics.IsEquivalent.tendsto_const** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u : α → β} 
{l : Filter α} {c : β},   Asymptotics.IsEquivalent l u (Function.const α c) → Fi
lter.Tendsto u l (nhds c)
参数：Function.const α c；nhds c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isEquivalent_zero_iff_eventually_zero`：isEquivalent_zero_iff
_eventually_zero : u ~[l] 0 ↔ u =ᶠ[l] 0
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isEquivalent_const_iff_tendsto`：isEquivalent_const_iff_tends
to {c : β} (h : c != 0) : u ~[l] const _ c ↔ Tendsto u l (𝓝 c)
-/
theorem IsEquivalent.tendsto_const {c : β} (hu : u ~[l] const _ c) : Tendsto u l (𝓝 c) := by
  rcases em <| c = 0 with rfl | h
  · exact (tendsto_congr' <| isEquivalent_zero_iff_eventually_zero.mp hu).mpr tendsto_const_nhds
  · exact (isEquivalent_const_iff_tendsto h).mp hu
/-
**Asymptotics.IsEquivalent.tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.I
sEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u v : α → β
} {l : Filter α} {c : β},   Asymptotics.IsEquivalent l u v → Filter.Tendsto u l 
(nhds c) → Filter.Tendsto v l (nhds c)
参数：nhds c；nhds c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Asymptotics.IsLittleO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `Asymptotics.IsLittleO.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {l : Fi
lter α} {f : α → …
· 使用定理 `Asymptotics.IsEquivalent.isLittleO`：∀ {α : Type u_1} {β : Type u_2} [ins
t : NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivale
nt l u v → (u - v) =o[l]…
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
· 使用定理 `Asymptotics.isEquivalent_const_iff_tendsto`：isEquivalent_const_iff_tends
to {c : β} (h : c != 0) : u ~[l] const _ c ↔ Tendsto u l (𝓝 c)
· 使用定理 `Asymptotics.IsEquivalent.trans`：∀ {α : Type u_1} {β : Type u_2} [inst : 
NormedAddCommGroup β] {l : Filter α} {u v w : α → β},   Asymptotics.IsEquivalent
 l u v → Asymptotics…
-/
theorem IsEquivalent.tendsto_nhds {c : β} (huv : u ~[l] v) (hu : Tendsto u l (𝓝 c)) :
    Tendsto v l (𝓝 c) := by
  by_cases h : c = 0
  · subst c
    rw [← isLittleO_one_iff ℝ] at hu ⊢
    simpa using (huv.symm.isLittleO.trans hu).add hu
  · rw [← isEquivalent_const_iff_tendsto h] at hu ⊢
    exact huv.symm.trans hu
/-
**Asymptotics.IsEquivalent.tendsto_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptoti
cs.IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u v : α → β
} {l : Filter α} {c : β},   Asymptotics.IsEquivalent l u v → (Filter.Tendsto u l
 (nhds c) ↔ Filter.Tendsto v l (nhds c))
参数：Filter.Tendsto u l (nhds c) ↔ Filter.Tendsto v l (nhds c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.tendsto_nhds`：∀ {α : Type u_1} {β : Type u_2} [
inst : NormedAddCommGroup β] {u v : α → β} {l : Filter α} {c : β},   Asymptotics
.IsEquivalent l u v → Filte…
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
-/
theorem IsEquivalent.tendsto_nhds_iff {c : β} (huv : u ~[l] v) :
    Tendsto u l (𝓝 c) ↔ Tendsto v l (𝓝 c) :=
  ⟨huv.tendsto_nhds, huv.symm.tendsto_nhds⟩
/-
**Asymptotics.IsEquivalent.add_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u v w : α →
 β} {l : Filter α},   Asymptotics.IsEquivalent l u v → w =o[l] v → Asymptotics.I
sEquivalent l (u + w) v
参数：u + w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_right_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a + b - c = a - c + b
· 使用定理 `Asymptotics.IsLittleO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
-/
theorem IsEquivalent.add_isLittleO (huv : u ~[l] v) (hwv : w =o[l] v) : u + w ~[l] v := by
  simpa only [IsEquivalent, add_sub_right_comm] using! huv.add hwv
/-
**Asymptotics.IsEquivalent.sub_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u v w : α →
 β} {l : Filter α},   Asymptotics.IsEquivalent l u v → w =o[l] v → Asymptotics.I
sEquivalent l (u - w) v
参数：u - w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Asymptotics.IsEquivalent.add_isLittleO`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedAddCommGroup β] {u v w : α → β} {l : Filter α},   Asymptotics.IsEq
uivalent l u v → w =o[l] v →…
· 使用定理 `Asymptotics.IsLittleO.neg_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Ty
pe u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' :
 α → E'} {l : Filter…
-/
theorem IsEquivalent.sub_isLittleO (huv : u ~[l] v) (hwv : w =o[l] v) : u - w ~[l] v := by
  simpa only [sub_eq_add_neg] using! huv.add_isLittleO hwv.neg_left
/-
**Asymptotics.IsLittleO.add_isEquivalent** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsLittleO`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u v w : α →
 β} {l : Filter α},   u =o[l] w → Asymptotics.IsEquivalent l v w → Asymptotics.I
sEquivalent l (u + v) w
参数：u + v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.add_isLittleO`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedAddCommGroup β] {u v w : α → β} {l : Filter α},   Asymptotics.IsEq
uivalent l u v → w =o[l] v →…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem IsLittleO.add_isEquivalent (hu : u =o[l] w) (hv : v ~[l] w) : u + v ~[l] w :=
  add_comm v u ▸ hv.add_isLittleO hu
/-
**Asymptotics.IsEquivalent.add_const_of_norm_tendsto_atTop** 是 Mathlib 中的一个定理，位于
命名空间 `Asymptotics.IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u v : α → β
} {l : Filter α} {c : β},   Asymptotics.IsEquivalent l u v →     Filter.Tendsto 
(norm ∘ v) l Filter.atTop → Asymptotics.IsEquivalent l (fun x => u x + c) v
参数：norm ∘ v；fun x => u x + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.add_isLittleO`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedAddCommGroup β] {u v w : α → β} {l : Filter α},   Asymptotics.IsEq
uivalent l u v → w =o[l] v →…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_const_left`：isLittleO_const_left {c : E''} : (fun 
_x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop
-/
theorem IsEquivalent.add_const_of_norm_tendsto_atTop {c : β}
    (huv : u ~[l] v) (hv : Tendsto (norm ∘ v) l atTop) :
    (u · + c) ~[l] v :=
  huv.add_isLittleO <| isLittleO_const_left.mpr (Or.inr hv)
/-
**Asymptotics.IsEquivalent.const_add_of_norm_tendsto_atTop** 是 Mathlib 中的一个定理，位于
命名空间 `Asymptotics.IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u v : α → β
} {l : Filter α} {c : β},   Asymptotics.IsEquivalent l u v →     Filter.Tendsto 
(norm ∘ v) l Filter.atTop → Asymptotics.IsEquivalent l (fun x => c + u x) v
参数：norm ∘ v；fun x => c + u x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.add_isEquivalent`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedAddCommGroup β] {u v w : α → β} {l : Filter α},   u =o[l] w → Asym
ptotics.IsEquivalent l v w →…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_const_left`：isLittleO_const_left {c : E''} : (fun 
_x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop
-/
theorem IsEquivalent.const_add_of_norm_tendsto_atTop {c : β}
    (huv : u ~[l] v) (hv : Tendsto (norm ∘ v) l atTop) :
    (c + u ·) ~[l] v :=
  (isLittleO_const_left.mpr (Or.inr hv)).add_isEquivalent huv
/-
**Asymptotics.IsLittleO.isEquivalent** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLi
ttleO`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u v : α → β
} {l : Filter α},   (u - v) =o[l] v → Asymptotics.IsEquivalent l u v
参数：u - v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsLittleO.isEquivalent (huv : (u - v) =o[l] v) : u ~[l] v := huv
/-
**Asymptotics.IsEquivalent.neg** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsEquivale
nt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {u v : α → β
} {l : Filter α},   Asymptotics.IsEquivalent l u v → Asymptotics.IsEquivalent l 
(fun x => -u x) fun x => -v x
参数：fun x => -u x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsEquivalent.eq_1`：∀ {α : Type u_1} {E' : Type u_6} [inst : 
SeminormedAddCommGroup E'] (l : Filter α) (u v : α → E'),   Asymptotics.IsEquiva
lent l u v = (u - v…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsLittleO.neg_right`：∀ {α : Type u_1} {E : Type u_3} {F' : T
ype u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' 
: α → F'} {l : Filter…
· 使用定理 `Asymptotics.IsLittleO.neg_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Ty
pe u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' :
 α → E'} {l : Filter…
· 使用定理 `Asymptotics.IsEquivalent.isLittleO`：∀ {α : Type u_1} {β : Type u_2} [ins
t : NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivale
nt l u v → (u - v) =o[l]…
-/
theorem IsEquivalent.neg (huv : u ~[l] v) : (fun x ↦ -u x) ~[l] fun x ↦ -v x := by
  rw [IsEquivalent]
  convert! huv.isLittleO.neg_left.neg_right
  simp [neg_add_eq_sub]

end NormedAddCommGroup

open Asymptotics

section NormedField

variable {α β : Type*} [NormedField β] {u v : α → β} {l : Filter α}

/-
**Asymptotics.isEquivalent_iff_exists_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics`。
形式化陈述：isEquivalent_iff_exists_eq_mul : u ~[l] v ↔ exists (φ : α -> β) (_ : Tends
to φ l (𝓝 1)), u =ᶠ[l] φ * v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsEquivalent.eq_1`：∀ {α : Type u_1} {E' : Type u_6} [inst : 
SeminormedAddCommGroup E'] (l : Filter α) (u v : α → E'),   Asymptotics.IsEquiva
lent l u v = (u - v…
· 使用定理 `Asymptotics.isLittleO_iff_exists_eq_mul`：isLittleO_iff_exists_eq_mul : u
 =o[l] v ↔ exists φ : α -> 𝕜, Tendsto φ l (𝓝 0) ∧ u =ᶠ[l] φ * v
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Filter.EventuallyEq.fun_add`：∀ {α : Type u} {β : Type v} [inst : Add β] 
{f f' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → (fun i => f i + 
f' i) =ᶠ[l] fun i…
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Filter.EventuallyEq.fun_sub`：∀ {α : Type u} {β : Type v} [inst : Sub β] 
{f f' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → (fun i => f i - 
f' i) =ᶠ[l] fun i…
-/
theorem isEquivalent_iff_exists_eq_mul :
    u ~[l] v ↔ ∃ (φ : α → β) (_ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v := by
  rw [IsEquivalent, isLittleO_iff_exists_eq_mul]
  constructor <;> rintro ⟨φ, hφ, h⟩ <;> [refine ⟨φ + 1, ?_, ?_⟩; refine ⟨φ - 1, ?_, ?_⟩]
  · conv in 𝓝 _ => rw [← zero_add (1 : β)]
    exact hφ.add tendsto_const_nhds
  · convert! h.fun_add (EventuallyEq.refl l v) <;> simp [add_mul]
  · conv in 𝓝 _ => rw [← sub_self (1 : β)]
    exact hφ.sub tendsto_const_nhds
  · convert! h.fun_sub (EventuallyEq.refl l v); simp [sub_mul]
/-
**Asymptotics.IsEquivalent.exists_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedField β] {u v : α → β} {l : 
Filter α},   Asymptotics.IsEquivalent l u v → ∃ φ, ∃ (_ : Filter.Tendsto φ l (nh
ds 1)), u =ᶠ[l] φ * v
参数：_ : Filter.Tendsto φ l (nhds 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isEquivalent_iff_exists_eq_mul`：isEquivalent_iff_exists_eq_m
ul : u ~[l] v ↔ exists (φ : α -> β) (_ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v
-/
theorem IsEquivalent.exists_eq_mul (huv : u ~[l] v) :
    ∃ (φ : α → β) (_ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v :=
  isEquivalent_iff_exists_eq_mul.mp huv
/-
**Asymptotics.isEquivalent_of_tendsto_one** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics
`。
形式化陈述：isEquivalent_of_tendsto_one (huv : Tendsto (u / v) l (𝓝 1)) : u ~[l] v
参数：huv : Tendsto (u / v) l (𝓝 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `tendsto_nhds_unique_of_frequently_eq`：tendsto_nhds_unique_of_frequently_
eq [T2Space X] {f g : Y -> X} {l : Filter Y} {a b : X} (ha : Tendsto f l (𝓝 a)) 
(hb : Tendsto g l (𝓝 b)) (…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Asymptotics.isEquivalent_iff_exists_eq_mul`：isEquivalent_iff_exists_eq_m
ul : u ~[l] v ↔ exists (φ : α -> β) (_ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_mul_cancel_of_imp`：div_mul_cancel_of_imp (h : b = 0 -> a = 0) : a / 
b * b = a
-/
theorem isEquivalent_of_tendsto_one (huv : Tendsto (u / v) l (𝓝 1)) :
    u ~[l] v := by
  suffices ∀ᶠ x in l, v x = 0 → u x = 0 by
    rw [isEquivalent_iff_exists_eq_mul]
    exact ⟨u / v, huv, this.mono fun x hz' ↦ (div_mul_cancel_of_imp hz').symm⟩
  by_contra! h
  replace h : ∃ᶠ t in l, (u / v) t = 0 := h.mono fun x ⟨hv, hu⟩ ↦ by simp [hv]
  simpa using tendsto_nhds_unique_of_frequently_eq (b := 0) huv tendsto_const_nhds h

@[deprecated (since := "2026-01-26")] alias isEquivalent_of_tendsto_one' :=
  isEquivalent_of_tendsto_one
/-
**Asymptotics.isEquivalent_iff_tendsto_one** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotic
s`。
形式化陈述：isEquivalent_iff_tendsto_one (hz : forallᶠ x in l, v x != 0) : u ~[l] v ↔ 
Tendsto (u / v) l (𝓝 1)
参数：hz : forallᶠ x in l, v x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.tendsto_div_nhds_zero`：∀ {α : Type u_1} {𝕜 : Type 
u_15} [inst : NormedDivisionRing 𝕜] {l : Filter α} {f g : α → 𝕜},   f =o[l] g → 
Filter.Tendsto (fun x => f x / g …
· 使用定理 `Asymptotics.IsEquivalent.isLittleO`：∀ {α : Type u_1} {β : Type u_2} [ins
t : NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivale
nt l u v → (u - v) =o[l]…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `Asymptotics.isEquivalent_of_tendsto_one`：isEquivalent_of_tendsto_one (hu
v : Tendsto (u / v) l (𝓝 1)) : u ~[l] v
-/
theorem isEquivalent_iff_tendsto_one (hz : ∀ᶠ x in l, v x ≠ 0) :
    u ~[l] v ↔ Tendsto (u / v) l (𝓝 1) := by
  constructor
  · intro hequiv
    have := hequiv.isLittleO.tendsto_div_nhds_zero
    simp only [Pi.sub_apply, sub_div] at this
    have key : Tendsto (fun x ↦ v x / v x) l (𝓝 1) :=
      (tendsto_congr' <| hz.mono fun x hnz ↦ @div_self _ _ (v x) hnz).mpr tendsto_const_nhds
    convert! this.add key
    · simp
    · simp
  · exact isEquivalent_of_tendsto_one

end NormedField

section SMul

/-
**Asymptotics.IsEquivalent.smul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsEquival
ent`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {𝕜 : Type u_3} [inst : NormedField 𝕜] [ins
t_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {a b : α → 𝕜} {u v : α 
→ E} {l : Filter α},   Asymptotics.IsEquivalent l a b →     Asymptotics.IsEquiva
lent l u v → Asymptotics.IsEquivalent l (fun x => a x • u x) fun x => b x • v x
参数：fun x => a x • u x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.exists_eq_mul`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedField β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent 
l u v → ∃ φ, ∃ (_ : Filter.T…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `Filter.EventuallyEq.fun_sub`：∀ {α : Type u} {β : Type v} [inst : Sub β] 
{f f' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → (fun i => f i - 
f' i) =ᶠ[l] fun i…
· 使用定理 `Filter.EventuallyEq.comp₂`：∀ {α : Type u} {β : Type v} {γ : Type w} {δ :
 Type u_2} {f f' : α → β} {g g' : α → γ} {l : Filter α},   f =ᶠ[l] f' → ∀ (h : β
 → γ → δ), g =ᶠ…
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isLittleO_congr`：isLittleO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁
 =ᶠ[l] g₂) : f₁ =o[l] g₁ ↔ f₂ =o[l] g₂
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
· 使用定理 `Asymptotics.IsBigO.smul_isLittleO`：∀ {α : Type u_1} {E' : Type u_6} {F' 
: Type u_7} {R : Type u_13} {𝕜' : Type u_16} [inst : SeminormedAddCommGroup E'] 
  [inst_1 : SeminormedA…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Asymptotics.IsBigO.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `Asymptotics.IsEquivalent.isBigO`：∀ {α : Type u_1} {β : Type u_2} [inst :
 NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent 
l u v → u =O[l] v
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
（共 118 条，此处仅展示前 30 条）
-/
theorem IsEquivalent.smul {α E 𝕜 : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {a b : α → 𝕜} {u v : α → E} {l : Filter α} (hab : a ~[l] b) (huv : u ~[l] v) :
    (fun x ↦ a x • u x) ~[l] fun x ↦ b x • v x := by
  rcases hab.exists_eq_mul with ⟨φ, hφ, habφ⟩
  have : ((fun x ↦ a x • u x) - (fun x ↦ b x • v x)) =ᶠ[l] fun x ↦ b x • (φ x • u x - v x) := by
    convert!
      (habφ.comp₂ (· • ·) <| EventuallyEq.refl _ u).fun_sub
        (EventuallyEq.refl _ fun x ↦ b x • v x) using 1
    ext
    rw [Pi.mul_apply, mul_comm, mul_smul, ← smul_sub]
  refine (isLittleO_congr this.symm <| EventuallyEq.rfl).mp ((isBigO_refl b l).smul_isLittleO ?_)
  rcases huv.isBigO.exists_pos with ⟨C, hC, hCuv⟩
  rw [IsEquivalent] at *
  rw [isLittleO_iff] at *
  rw [IsBigOWith] at hCuv
  simp only [Metric.tendsto_nhds, dist_eq_norm] at hφ
  intro c hc
  specialize hφ (c / 2 / C) (div_pos (div_pos hc zero_lt_two) hC)
  specialize huv (div_pos hc zero_lt_two)
  refine hφ.mp (huv.mp <| hCuv.mono fun x hCuvx huvx hφx ↦ ?_)
  have key :=
    calc
      ‖φ x - 1‖ * ‖u x‖ ≤ c / 2 / C * ‖u x‖ := by gcongr
      _ ≤ c / 2 / C * (C * ‖v x‖) := by gcongr
      _ = c / 2 * ‖v x‖ := by field
  calc
    ‖((fun x : α ↦ φ x • u x) - v) x‖ = ‖(φ x - 1) • u x + (u x - v x)‖ := by
      simp [sub_smul, sub_add]
    _ ≤ ‖(φ x - 1) • u x‖ + ‖u x - v x‖ := norm_add_le _ _
    _ = ‖φ x - 1‖ * ‖u x‖ + ‖u x - v x‖ := by rw [norm_smul]
    _ ≤ c / 2 * ‖v x‖ + ‖u x - v x‖ := by gcongr
    _ ≤ c / 2 * ‖v x‖ + c / 2 * ‖v x‖ := by gcongr; exact huvx
    _ = c * ‖v x‖ := by ring

end SMul

section mul_inv

variable {α ι β : Type*} [NormedField β] {t u v w : α → β} {l : Filter α}

/-
**Asymptotics.IsEquivalent.mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsEquivale
nt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_3} [inst : NormedField β] {t u v w : α → β} {
l : Filter α},   Asymptotics.IsEquivalent l t u → Asymptotics.IsEquivalent l v w
 → Asymptotics.IsEquivalent l (t * v) (u * w)
参数：t * v；u * w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.smul`：∀ {α : Type u_1} {E : Type u_2} {𝕜 : Type
 u_3} [inst : NormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {a b : α …
-/
protected theorem IsEquivalent.mul (htu : t ~[l] u) (hvw : v ~[l] w) : t * v ~[l] u * w :=
  htu.smul hvw
/-
**Asymptotics.IsEquivalent.listProd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsEqu
ivalent`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {β : Type u_3} [inst : NormedField β] {l :
 Filter α} {L : List ι} {f g : ι → α → β},   (∀ i ∈ L, Asymptotics.IsEquivalent 
l (f i) (g i)) →     Asymptotics.IsEquivalent l (fun x => (List.map (fun x_1 => 
f x_1 x) L).prod) fun x =>       (List.map (fun x_1 => g x_1 x) L).prod
参数：∀ i ∈ L, Asymptotics.IsEquivalent l (f i) (g i)；fun x => (List.map (fun x_1 =
> f x_1 x) L).prod；List.map (fun x_1 => g x_1 x) L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Asymptotics.IsEquivalent.mul`：∀ {α : Type u_1} {β : Type u_3} [inst : No
rmedField β] {t u v w : α → β} {l : Filter α},   Asymptotics.IsEquivalent l t u 
→ Asymptotics.IsEq…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsEquivalent.listProd {L : List ι} {f g : ι → α → β} (h : ∀ i ∈ L, f i ~[l] g i) :
    (fun x ↦ (L.map (f · x)).prod) ~[l] (fun x ↦ (L.map (g · x)).prod) := by
  induction L with
  | nil => simp [IsEquivalent.refl]
  | cons i L ihL =>
    simp only [List.forall_mem_cons, List.map_cons, List.prod_cons] at h ⊢
    exact h.1.mul (ihL h.2)
/-
**Asymptotics.IsEquivalent.multisetProd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.I
sEquivalent`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {β : Type u_3} [inst : NormedField β] {l :
 Filter α} {s : Multiset ι} {f g : ι → α → β},   (∀ i ∈ s, Asymptotics.IsEquival
ent l (f i) (g i)) →     Asymptotics.IsEquivalent l (fun x => (Multiset.map (fun
 x_1 => f x_1 x) s).prod) fun x =>       (Multiset.map (fun x_1 => g x_1 x) s).p
rod
参数：∀ i ∈ s, Asymptotics.IsEquivalent l (f i) (g i)；fun x => (Multiset.map (fun x
_1 => f x_1 x) s).prod；Multiset.map (fun x_1 => g x_1 x) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk_surjective`：Quotient.mk_surjective {s : Setoid α} : Function
.Surjective (Quotient.mk s)
· 使用定理 `Asymptotics.IsEquivalent.listProd`：∀ {α : Type u_1} {ι : Type u_2} {β : 
Type u_3} [inst : NormedField β] {l : Filter α} {L : List ι} {f g : ι → α → β}, 
  (∀ i ∈ L, Asymptotics…
-/
theorem IsEquivalent.multisetProd {s : Multiset ι} {f g : ι → α → β} (h : ∀ i ∈ s, f i ~[l] g i) :
    (fun x ↦ (s.map (f · x)).prod) ~[l] (fun x ↦ (s.map (g · x)).prod) := by
  obtain ⟨l, rfl⟩ : ∃ l : List ι, ↑l = s := Quotient.mk_surjective s
  exact listProd h
/-
**Asymptotics.IsEquivalent.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsE
quivalent`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {β : Type u_3} [inst : NormedField β] {l :
 Filter α} {s : Finset ι} {f g : ι → α → β},   (∀ i ∈ s, Asymptotics.IsEquivalen
t l (f i) (g i)) →     Asymptotics.IsEquivalent l (fun x => ∏ i ∈ s, f i x) fun 
x => ∏ i ∈ s, g i x
参数：∀ i ∈ s, Asymptotics.IsEquivalent l (f i) (g i)；fun x => ∏ i ∈ s, f i x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.multisetProd`：∀ {α : Type u_1} {ι : Type u_2} {
β : Type u_3} [inst : NormedField β] {l : Filter α} {s : Multiset ι} {f g : ι → 
α → β},   (∀ i ∈ s, Asympto…
-/
theorem IsEquivalent.finsetProd {s : Finset ι} {f g : ι → α → β} (h : ∀ i ∈ s, f i ~[l] g i) :
    (∏ i ∈ s, f i ·) ~[l] (∏ i ∈ s, g i ·) :=
  multisetProd h
/-
**Asymptotics.IsEquivalent.inv** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsEquivale
nt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_3} [inst : NormedField β] {u v : α → β} {l : 
Filter α},   Asymptotics.IsEquivalent l u v → Asymptotics.IsEquivalent l u⁻¹ v⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isEquivalent_iff_exists_eq_mul`：isEquivalent_iff_exists_eq_m
ul : u ~[l] v ↔ exists (φ : α -> β) (_ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Filter.Tendsto.inv₀`：Filter.Tendsto.inv₀ {a : G₀} (hf : Tendsto f l (𝓝 a
)) (ha : a != 0) : Tendsto (fun x => (f x)⁻¹) l (𝓝 a⁻¹)
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.EventuallyEq.fun_inv`：∀ {α : Type u} {β : Type v} [inst : Inv β] 
{f g : α → β} {l : Filter α},   f =ᶠ[l] g → (fun i => (f i)⁻¹) =ᶠ[l] fun i => (g
 i)⁻¹
-/
protected theorem IsEquivalent.inv (huv : u ~[l] v) : u⁻¹ ~[l] v⁻¹ := by
  rw [isEquivalent_iff_exists_eq_mul] at *
  rcases huv with ⟨φ, hφ, h⟩
  rw [← inv_one]
  refine ⟨fun x ↦ (φ x)⁻¹, Tendsto.inv₀ hφ (by simp), ?_⟩
  convert! h.fun_inv
  simp [mul_comm]
/-
**Asymptotics.IsEquivalent.div** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsEquivale
nt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_3} [inst : NormedField β] {t u v w : α → β} {
l : Filter α},   Asymptotics.IsEquivalent l t u → Asymptotics.IsEquivalent l v w
 → Asymptotics.IsEquivalent l (t / v) (u / w)
参数：t / v；u / w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Asymptotics.IsEquivalent.mul`：∀ {α : Type u_1} {β : Type u_3} [inst : No
rmedField β] {t u v w : α → β} {l : Filter α},   Asymptotics.IsEquivalent l t u 
→ Asymptotics.IsEq…
· 使用定理 `Asymptotics.IsEquivalent.inv`：∀ {α : Type u_1} {β : Type u_3} [inst : No
rmedField β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l u v → As
ymptotics.IsEquiva…
-/
protected theorem IsEquivalent.div (htu : t ~[l] u) (hvw : v ~[l] w) :
    t / v ~[l] u / w := by
  simpa only [div_eq_mul_inv] using htu.mul hvw.inv
/-
**Asymptotics.IsEquivalent.pow** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsEquivale
nt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_3} [inst : NormedField β] {t u : α → β} {l : 
Filter α},   Asymptotics.IsEquivalent l t u → ∀ (n : ℕ), Asymptotics.IsEquivalen
t l (t ^ n) (u ^ n)
参数：n : ℕ；t ^ n；u ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Asymptotics.IsEquivalent.refl`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u : α → β} {l : Filter α}, Asymptotics.IsEquivalent l u u
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Asymptotics.IsEquivalent.mul`：∀ {α : Type u_1} {β : Type u_3} [inst : No
rmedField β] {t u v w : α → β} {l : Filter α},   Asymptotics.IsEquivalent l t u 
→ Asymptotics.IsEq…
-/
protected theorem IsEquivalent.pow (h : t ~[l] u) (n : ℕ) : t ^ n ~[l] u ^ n := by
  induction n with
  | zero => simpa using IsEquivalent.refl
  | succ _ ih => simpa [pow_succ] using ih.mul h
/-
**Asymptotics.IsEquivalent.zpow** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsEquival
ent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_3} [inst : NormedField β] {t u : α → β} {l : 
Filter α},   Asymptotics.IsEquivalent l t u → ∀ (z : ℤ), Asymptotics.IsEquivalen
t l (t ^ z) (u ^ z)
参数：z : ℤ；t ^ z；u ^ z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Asymptotics.IsEquivalent.pow`：∀ {α : Type u_1} {β : Type u_3} [inst : No
rmedField β] {t u : α → β} {l : Filter α},   Asymptotics.IsEquivalent l t u → ∀ 
(n : ℕ), Asymptoti…
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Asymptotics.IsEquivalent.inv`：∀ {α : Type u_1} {β : Type u_3} [inst : No
rmedField β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l u v → As
ymptotics.IsEquiva…
-/
protected theorem IsEquivalent.zpow (h : t ~[l] u) (z : ℤ) : t ^ z ~[l] u ^ z := by
  match z with
  | Int.ofNat _ => simpa using h.pow _
  | Int.negSucc _ => simpa using (h.pow _).inv

end mul_inv

section NormedLinearOrderedField

variable {α β : Type*} [NormedField β] [LinearOrder β] [IsStrictOrderedRing β]
  {u v : α → β} {l : Filter α}

/-
**Asymptotics.IsEquivalent.tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedField β] [inst_1 : LinearOrd
er β] [IsStrictOrderedRing β] {u v : α → β}   {l : Filter α} [OrderTopology β], 
  Asymptotics.IsEquivalent l u v → Filter.Tendsto u l Filter.atTop → Filter.Tend
sto v l Filter.atTop
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.exists_eq_mul`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedField β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent 
l u v → ∃ φ, ∃ (_ : Filter.T…
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.Tendsto.atTop_mul_pos`：Filter.Tendsto.atTop_mul_pos {C : 𝕜} (hC :
 0 < C) (hf : Tendsto f l atTop) (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f 
x * g x) l atTop
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem IsEquivalent.tendsto_atTop [OrderTopology β] (huv : u ~[l] v) (hu : Tendsto u l atTop) :
    Tendsto v l atTop :=
  let ⟨φ, hφ, h⟩ := huv.symm.exists_eq_mul
  Tendsto.congr' h.symm (mul_comm u φ ▸ hu.atTop_mul_pos zero_lt_one hφ)
/-
**Asymptotics.IsEquivalent.tendsto_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics.IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedField β] [inst_1 : LinearOrd
er β] [IsStrictOrderedRing β] {u v : α → β}   {l : Filter α} [OrderTopology β], 
  Asymptotics.IsEquivalent l u v → (Filter.Tendsto u l Filter.atTop ↔ Filter.Ten
dsto v l Filter.atTop)
参数：Filter.Tendsto u l Filter.atTop ↔ Filter.Tendsto v l Filter.atTop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.tendsto_atTop`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedField β] [inst_1 : LinearOrder β] [IsStrictOrderedRing β] {u v : α
 → β}   {l : Filter α} [Orde…
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
-/
theorem IsEquivalent.tendsto_atTop_iff [OrderTopology β] (huv : u ~[l] v) :
    Tendsto u l atTop ↔ Tendsto v l atTop :=
  ⟨huv.tendsto_atTop, huv.symm.tendsto_atTop⟩
/-
**Asymptotics.IsEquivalent.tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedField β] [inst_1 : LinearOrd
er β] [IsStrictOrderedRing β] {u v : α → β}   {l : Filter α} [OrderTopology β], 
  Asymptotics.IsEquivalent l u v → Filter.Tendsto u l Filter.atBot → Filter.Tend
sto v l Filter.atBot
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_neg_atTop_atBot`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atTop Filter.atBo…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Asymptotics.IsEquivalent.tendsto_atTop`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedField β] [inst_1 : LinearOrder β] [IsStrictOrderedRing β] {u v : α
 → β}   {l : Filter α} [Orde…
· 使用定理 `Asymptotics.IsEquivalent.neg`：∀ {α : Type u_1} {β : Type u_2} [inst : No
rmedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l u
 v → Asymptotics.I…
· 使用定理 `Filter.tendsto_neg_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atBot Filter.atTo…
-/
theorem IsEquivalent.tendsto_atBot [OrderTopology β] (huv : u ~[l] v) (hu : Tendsto u l atBot) :
    Tendsto v l atBot := by
  convert! tendsto_neg_atTop_atBot.comp (huv.neg.tendsto_atTop <| tendsto_neg_atBot_atTop.comp hu)
  ext
  simp
/-
**Asymptotics.IsEquivalent.tendsto_atBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics.IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedField β] [inst_1 : LinearOrd
er β] [IsStrictOrderedRing β] {u v : α → β}   {l : Filter α} [OrderTopology β], 
  Asymptotics.IsEquivalent l u v → (Filter.Tendsto u l Filter.atBot ↔ Filter.Ten
dsto v l Filter.atBot)
参数：Filter.Tendsto u l Filter.atBot ↔ Filter.Tendsto v l Filter.atBot。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.tendsto_atBot`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedField β] [inst_1 : LinearOrder β] [IsStrictOrderedRing β] {u v : α
 → β}   {l : Filter α} [Orde…
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
-/
theorem IsEquivalent.tendsto_atBot_iff [OrderTopology β] (huv : u ~[l] v) :
    Tendsto u l atBot ↔ Tendsto v l atBot :=
  ⟨huv.tendsto_atBot, huv.symm.tendsto_atBot⟩

section ClosedIicTopology

variable [ClosedIicTopology β]

/-
**Asymptotics.IsEquivalent.exists_pos_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics.IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedField β] [inst_1 : LinearOrd
er β] [IsStrictOrderedRing β] {u v : α → β}   {l : Filter α} [ClosedIicTopology 
β], Asymptotics.IsEquivalent l u v → ∃ φ, (∀ᶠ (x : α) in l, 0 < φ x) ∧ u =ᶠ[l] φ
 * v
参数：∀ᶠ (x : α) in l, 0 < φ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.exists_eq_mul`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedField β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent 
l u v → ∃ φ, ∃ (_ : Filter.T…
· 使用定理 `Filter.Tendsto.eventually_const_lt`：Filter.Tendsto.eventually_const_lt {
l : Filter γ} {f : γ -> α} {u v : α} (hv : u < v) (h : Filter.Tendsto f l (𝓝 v))
 : forallᶠ a in l, u < f…
· 使用引理 `zero_lt_one'`：zero_lt_one' : (0 : α) < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
lemma IsEquivalent.exists_pos_eq_mul (h : u ~[l] v) :
    ∃ φ, (∀ᶠ x in l, 0 < φ x) ∧ (u =ᶠ[l] φ * v) := by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_eq_mul
  exact ⟨φ, hφ.eventually_const_lt (zero_lt_one' β), h_eq⟩
/-
**Asymptotics.IsEquivalent.eventually_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics.IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedField β] [inst_1 : LinearOrd
er β] [IsStrictOrderedRing β] {u v : α → β}   {l : Filter α} [ClosedIicTopology 
β],   Asymptotics.IsEquivalent l u v → (∀ᶠ (t : α) in l, 0 ≤ v t) → ∀ᶠ (x : α) i
n l, 0 ≤ u x
参数：∀ᶠ (t : α) in l, 0 ≤ v t；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.exists_pos_eq_mul`：∀ {α : Type u_1} {β : Type u
_2} [inst : NormedField β] [inst_1 : LinearOrder β] [IsStrictOrderedRing β] {u v
 : α → β}   {l : Filter α} [Clos…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsEquivalent.eventually_nonneg (h : u ~[l] v) (hv : ∀ᶠ t in l, 0 ≤ v t) :
    ∀ᶠ x in l, 0 ≤ u x := by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_pos_eq_mul
  exact (hφ.and (hv.and h_eq)).mono (fun x ⟨hφ, hv, h_eq⟩ ↦ h_eq ▸ mul_nonneg hφ.le hv)
/-
**Asymptotics.IsEquivalent.eventually_pos** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics
.IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedField β] [inst_1 : LinearOrd
er β] [IsStrictOrderedRing β] {u v : α → β}   {l : Filter α} [ClosedIicTopology 
β],   Asymptotics.IsEquivalent l u v → (∀ᶠ (t : α) in l, 0 < v t) → ∀ᶠ (x : α) i
n l, 0 < u x
参数：∀ᶠ (t : α) in l, 0 < v t；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.exists_pos_eq_mul`：∀ {α : Type u_1} {β : Type u
_2} [inst : NormedField β] [inst_1 : LinearOrder β] [IsStrictOrderedRing β] {u v
 : α → β}   {l : Filter α} [Clos…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsEquivalent.eventually_pos (h : u ~[l] v) (hv : ∀ᶠ t in l, 0 < v t) :
    ∀ᶠ x in l, 0 < u x := by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_pos_eq_mul
  exact (hφ.and (hv.and h_eq)).mono (fun x ⟨hφ, hv, h_eq⟩ ↦ h_eq ▸ mul_pos hφ hv)
/-
**Asymptotics.IsEquivalent.eventually_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics.IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedField β] [inst_1 : LinearOrd
er β] [IsStrictOrderedRing β] {u v : α → β}   {l : Filter α} [ClosedIicTopology 
β],   Asymptotics.IsEquivalent l u v → (∀ᶠ (t : α) in l, v t ≤ 0) → ∀ᶠ (x : α) i
n l, u x ≤ 0
参数：∀ᶠ (t : α) in l, v t ≤ 0；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.exists_pos_eq_mul`：∀ {α : Type u_1} {β : Type u
_2} [inst : NormedField β] [inst_1 : LinearOrder β] [IsStrictOrderedRing β] {u v
 : α → β}   {l : Filter α} [Clos…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `mul_nonpos_of_nonneg_of_nonpos`：mul_nonpos_of_nonneg_of_nonpos [PosMulMo
no α] (ha : 0 <= a) (hb : b <= 0) : a * b <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsEquivalent.eventually_nonpos (h : u ~[l] v) (hv : ∀ᶠ t in l, v t ≤ 0) :
    ∀ᶠ x in l, u x ≤ 0 := by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_pos_eq_mul
  exact (hφ.and (hv.and h_eq)).mono (fun x ⟨hφ, hv, h_eq⟩ ↦
    h_eq ▸ mul_nonpos_of_nonneg_of_nonpos hφ.le hv)
/-
**Asymptotics.IsEquivalent.eventually_neg** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics
.IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedField β] [inst_1 : LinearOrd
er β] [IsStrictOrderedRing β] {u v : α → β}   {l : Filter α} [ClosedIicTopology 
β],   Asymptotics.IsEquivalent l u v → (∀ᶠ (t : α) in l, v t < 0) → ∀ᶠ (x : α) i
n l, u x < 0
参数：∀ᶠ (t : α) in l, v t < 0；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.exists_pos_eq_mul`：∀ {α : Type u_1} {β : Type u
_2} [inst : NormedField β] [inst_1 : LinearOrder β] [IsStrictOrderedRing β] {u v
 : α → β}   {l : Filter α} [Clos…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `mul_neg_of_pos_of_neg`：mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 
0 < a) (hb : b < 0) : a * b < 0
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsEquivalent.eventually_neg (h : u ~[l] v) (hv : ∀ᶠ t in l, v t < 0) :
    ∀ᶠ x in l, u x < 0 := by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_pos_eq_mul
  exact (hφ.and (hv.and h_eq)).mono (fun x ⟨hφ, hv, h_eq⟩ ↦ h_eq ▸ mul_neg_of_pos_of_neg hφ hv)

end ClosedIicTopology

end NormedLinearOrderedField

section Real

/-
**Asymptotics.IsEquivalent.add_add_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics.IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {u v t w : α → ℝ} {l : Filter α},   0 ≤ v →     0 ≤ w → A
symptotics.IsEquivalent l u v → Asymptotics.IsEquivalent l t w → Asymptotics.IsE
quivalent l (u + t) (v + w)
参数：u + t；v + w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
· 使用定理 `Asymptotics.IsLittleO.add_add`：∀ {α : Type u_1} {E' : Type u_6} {F' : Ty
pe u_7} [inst : SeminormedAddCommGroup E'] [inst_1 : SeminormedAddCommGroup F'] 
  {l : Filter α} {f…
-/
theorem IsEquivalent.add_add_of_nonneg {α : Type*} {u v t w : α → ℝ} {l : Filter α}
    (hu : 0 ≤ v) (hw : 0 ≤ w) (htu : u ~[l] v) (hvw : t ~[l] w) :
    u + t ~[l] v + w := by
  simp only [IsEquivalent, add_sub_add_comm]
  change (fun x ↦ (u - v) x + (t - w) x) =o[l] (fun x ↦ v x + w x)
  conv => enter [3, x]; rw [← abs_eq_self.mpr (hu x), ← abs_eq_self.mpr (hw x)]
  simpa [← Real.norm_eq_abs] using .add_add htu hvw

end Real

end Asymptotics

open Filter Asymptotics

open Asymptotics

variable {α β β₂ : Type*} [NormedAddCommGroup β] [Norm β₂] {l : Filter α}

/-
**Filter.EventuallyEq.isEquivalent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.isEquivalent {u v : α -> β} (h : u =ᶠ[l] v) : u ~[l] v
参数：h : u =ᶠ[l] v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.congr_right`：∀ {α : Type u_1} {β : Type u_2} [i
nst : NormedAddCommGroup β] {u v w : α → β} {l : Filter α},   Asymptotics.IsEqui
valent l u v → v =ᶠ[l] w →…
· 使用定理 `Asymptotics.isLittleO_refl_left`：isLittleO_refl_left : (fun x => f' x - 
f' x) =o[l] g'
-/
theorem Filter.EventuallyEq.isEquivalent {u v : α → β} (h : u =ᶠ[l] v) : u ~[l] v :=
  IsEquivalent.congr_right (isLittleO_refl_left _ _) h

@[trans]
/-
**Filter.EventuallyEq.trans_isEquivalent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.trans_isEquivalent {f g₁ g₂ : α -> β} (h : f =ᶠ[l] g₁)
 (h₂ : g₁ ~[l] g₂) : f ~[l] g₂
参数：h : f =ᶠ[l] g₁；h₂ : g₁ ~[l] g₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.trans`：∀ {α : Type u_1} {β : Type u_2} [inst : 
NormedAddCommGroup β] {l : Filter α} {u v w : α → β},   Asymptotics.IsEquivalent
 l u v → Asymptotics…
· 使用定理 `Filter.EventuallyEq.isEquivalent`：Filter.EventuallyEq.isEquivalent {u v 
: α -> β} (h : u =ᶠ[l] v) : u ~[l] v
-/
theorem Filter.EventuallyEq.trans_isEquivalent {f g₁ g₂ : α → β} (h : f =ᶠ[l] g₁)
    (h₂ : g₁ ~[l] g₂) : f ~[l] g₂ :=
  h.isEquivalent.trans h₂

namespace Asymptotics

/-
**Asymptotics.transIsEquivalentIsEquivalent** 是 Mathlib 中的一个实例，位于命名空间 `Asymptoti
cs`。
形式化陈述：transIsEquivalentIsEquivalent : @Trans (α -> β) (α -> β) (α -> β) (IsEquiv
alent l) (IsEquivalent l) (IsEquivalent l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.trans`：∀ {α : Type u_1} {β : Type u_2} [inst : 
NormedAddCommGroup β] {l : Filter α} {u v w : α → β},   Asymptotics.IsEquivalent
 l u v → Asymptotics…
-/
instance transIsEquivalentIsEquivalent :
    @Trans (α → β) (α → β) (α → β) (IsEquivalent l) (IsEquivalent l) (IsEquivalent l) where
  trans := IsEquivalent.trans
/-
**Asymptotics.transEventuallyEqIsEquivalent** 是 Mathlib 中的一个实例，位于命名空间 `Asymptoti
cs`。
形式化陈述：transEventuallyEqIsEquivalent : @Trans (α -> β) (α -> β) (α -> β) (Eventua
llyEq l) (IsEquivalent l) (IsEquivalent l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans_isEquivalent`：Filter.EventuallyEq.trans_isEqui
valent {f g₁ g₂ : α -> β} (h : f =ᶠ[l] g₁) (h₂ : g₁ ~[l] g₂) : f ~[l] g₂
-/
instance transEventuallyEqIsEquivalent :
    @Trans (α → β) (α → β) (α → β) (EventuallyEq l) (IsEquivalent l) (IsEquivalent l) where
  trans := EventuallyEq.trans_isEquivalent

@[trans]
/-
**Asymptotics.IsEquivalent.trans_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 `Asympto
tics.IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {l : Filter 
α} {f g₁ g₂ : α → β},   Asymptotics.IsEquivalent l f g₁ → g₁ =ᶠ[l] g₂ → Asymptot
ics.IsEquivalent l f g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.trans`：∀ {α : Type u_1} {β : Type u_2} [inst : 
NormedAddCommGroup β] {l : Filter α} {u v w : α → β},   Asymptotics.IsEquivalent
 l u v → Asymptotics…
· 使用定理 `Filter.EventuallyEq.isEquivalent`：Filter.EventuallyEq.isEquivalent {u v 
: α -> β} (h : u =ᶠ[l] v) : u ~[l] v
-/
theorem IsEquivalent.trans_eventuallyEq {f g₁ g₂ : α → β} (h : f ~[l] g₁)
    (h₂ : g₁ =ᶠ[l] g₂) : f ~[l] g₂ :=
  h.trans h₂.isEquivalent
/-
**Asymptotics.transIsEquivalentEventuallyEq** 是 Mathlib 中的一个实例，位于命名空间 `Asymptoti
cs`。
形式化陈述：transIsEquivalentEventuallyEq : @Trans (α -> β) (α -> β) (α -> β) (IsEquiv
alent l) (EventuallyEq l) (IsEquivalent l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.trans_eventuallyEq`：∀ {α : Type u_1} {β : Type 
u_2} [inst : NormedAddCommGroup β] {l : Filter α} {f g₁ g₂ : α → β},   Asymptoti
cs.IsEquivalent l f g₁ → g₁ =ᶠ[l]…
-/
instance transIsEquivalentEventuallyEq :
    @Trans (α → β) (α → β) (α → β) (IsEquivalent l) (EventuallyEq l) (IsEquivalent l) where
  trans := IsEquivalent.trans_eventuallyEq

@[trans]
/-
**Asymptotics.IsEquivalent.trans_isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.I
sEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {β₂ : Type u_3} [inst : NormedAddCommGroup
 β] [inst_1 : Norm β₂] {l : Filter α}   {f g₁ : α → β} {g₂ : α → β₂}, Asymptotic
s.IsEquivalent l f g₁ → g₁ =O[l] g₂ → f =O[l] g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.IsEquivalent.isBigO`：∀ {α : Type u_1} {β : Type u_2} [inst :
 NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent 
l u v → u =O[l] v
-/
theorem IsEquivalent.trans_isBigO {f g₁ : α → β} {g₂ : α → β₂} (h : f ~[l] g₁) (h₂ : g₁ =O[l] g₂) :
    f =O[l] g₂ :=
  IsBigO.trans h.isBigO h₂
/-
**Asymptotics.transIsEquivalentIsBigO** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
形式化陈述：transIsEquivalentIsBigO : @Trans (α -> β) (α -> β) (α -> β₂) (IsEquivalent
 l) (IsBigO l) (IsBigO l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.trans_isBigO`：∀ {α : Type u_1} {β : Type u_2} {
β₂ : Type u_3} [inst : NormedAddCommGroup β] [inst_1 : Norm β₂] {l : Filter α}  
 {f g₁ : α → β} {g₂ : α → β…
-/
instance transIsEquivalentIsBigO :
    @Trans (α → β) (α → β) (α → β₂) (IsEquivalent l) (IsBigO l) (IsBigO l) where
  trans := IsEquivalent.trans_isBigO

@[trans]
/-
**Asymptotics.IsBigO.trans_isEquivalent** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.I
sBigO`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {β₂ : Type u_3} [inst : NormedAddCommGroup
 β] [inst_1 : Norm β₂] {l : Filter α}   {f : α → β₂} {g₁ g₂ : α → β}, f =O[l] g₁
 → Asymptotics.IsEquivalent l g₁ g₂ → f =O[l] g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.IsEquivalent.isBigO`：∀ {α : Type u_1} {β : Type u_2} [inst :
 NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent 
l u v → u =O[l] v
-/
theorem IsBigO.trans_isEquivalent {f : α → β₂} {g₁ g₂ : α → β} (h : f =O[l] g₁) (h₂ : g₁ ~[l] g₂) :
    f =O[l] g₂ :=
  IsBigO.trans h h₂.isBigO
/-
**Asymptotics.transIsBigOIsEquivalent** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
形式化陈述：transIsBigOIsEquivalent : @Trans (α -> β₂) (α -> β) (α -> β) (IsBigO l) (I
sEquivalent l) (IsBigO l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isEquivalent`：∀ {α : Type u_1} {β : Type u_2} {
β₂ : Type u_3} [inst : NormedAddCommGroup β] [inst_1 : Norm β₂] {l : Filter α}  
 {f : α → β₂} {g₁ g₂ : α → …
-/
instance transIsBigOIsEquivalent :
    @Trans (α → β₂) (α → β) (α → β) (IsBigO l) (IsEquivalent l) (IsBigO l) where
  trans := IsBigO.trans_isEquivalent

@[trans]
/-
**Asymptotics.IsEquivalent.trans_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotic
s.IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {β₂ : Type u_3} [inst : NormedAddCommGroup
 β] [inst_1 : Norm β₂] {l : Filter α}   {f g₁ : α → β} {g₂ : α → β₂}, Asymptotic
s.IsEquivalent l f g₁ → g₁ =o[l] g₂ → f =o[l] g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `Asymptotics.IsEquivalent.isBigO`：∀ {α : Type u_1} {β : Type u_2} [inst :
 NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent 
l u v → u =O[l] v
-/
theorem IsEquivalent.trans_isLittleO {f g₁ : α → β} {g₂ : α → β₂} (h : f ~[l] g₁)
    (h₂ : g₁ =o[l] g₂) : f =o[l] g₂ :=
  IsBigO.trans_isLittleO h.isBigO h₂
/-
**Asymptotics.transIsEquivalentIsLittleO** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`
。
形式化陈述：transIsEquivalentIsLittleO : @Trans (α -> β) (α -> β) (α -> β₂) (IsEquival
ent l) (IsLittleO l) (IsLittleO l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.trans_isLittleO`：∀ {α : Type u_1} {β : Type u_2
} {β₂ : Type u_3} [inst : NormedAddCommGroup β] [inst_1 : Norm β₂] {l : Filter α
}   {f g₁ : α → β} {g₂ : α → β…
-/
instance transIsEquivalentIsLittleO :
    @Trans (α → β) (α → β) (α → β₂) (IsEquivalent l) (IsLittleO l) (IsLittleO l) where
  trans := IsEquivalent.trans_isLittleO

@[trans]
/-
**Asymptotics.IsLittleO.trans_isEquivalent** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotic
s.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {β₂ : Type u_3} [inst : NormedAddCommGroup
 β] [inst_1 : Norm β₂] {l : Filter α}   {f : α → β₂} {g₁ g₂ : α → β}, f =o[l] g₁
 → Asymptotics.IsEquivalent l g₁ g₂ → f =o[l] g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
· 使用定理 `Asymptotics.IsEquivalent.isBigO`：∀ {α : Type u_1} {β : Type u_2} [inst :
 NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent 
l u v → u =O[l] v
-/
theorem IsLittleO.trans_isEquivalent {f : α → β₂} {g₁ g₂ : α → β} (h : f =o[l] g₁)
    (h₂ : g₁ ~[l] g₂) : f =o[l] g₂ :=
  IsLittleO.trans_isBigO h h₂.isBigO
/-
**Asymptotics.transIsLittleOIsEquivalent** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`
。
形式化陈述：transIsLittleOIsEquivalent : @Trans (α -> β₂) (α -> β) (α -> β) (IsLittleO
 l) (IsEquivalent l) (IsLittleO l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.trans_isEquivalent`：∀ {α : Type u_1} {β : Type u_2
} {β₂ : Type u_3} [inst : NormedAddCommGroup β] [inst_1 : Norm β₂] {l : Filter α
}   {f : α → β₂} {g₁ g₂ : α → …
-/
instance transIsLittleOIsEquivalent :
    @Trans (α → β₂) (α → β) (α → β) (IsLittleO l) (IsEquivalent l) (IsLittleO l) where
  trans := IsLittleO.trans_isEquivalent

@[trans]
/-
**Asymptotics.IsEquivalent.trans_isTheta** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {β₂ : Type u_3} [inst : NormedAddCommGroup
 β] [inst_1 : Norm β₂] {l : Filter α}   {f g₁ : α → β} {g₂ : α → β₂}, Asymptotic
s.IsEquivalent l f g₁ → g₁ =Θ[l] g₂ → f =Θ[l] g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5
} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddCom
mGroup F'] {l :…
· 使用定理 `Asymptotics.IsEquivalent.isTheta`：∀ {α : Type u_1} {β : Type u_2} [inst 
: NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent
 l u v → u =Θ[l] v
-/
theorem IsEquivalent.trans_isTheta {f g₁ : α → β} {g₂ : α → β₂} (h : f ~[l] g₁)
    (h₂ : g₁ =Θ[l] g₂) : f =Θ[l] g₂ :=
  IsTheta.trans h.isTheta h₂
/-
**Asymptotics.transIsEquivalentIsTheta** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
形式化陈述：transIsEquivalentIsTheta : @Trans (α -> β) (α -> β) (α -> β₂) (IsEquivalen
t l) (IsTheta l) (IsTheta l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.trans_isTheta`：∀ {α : Type u_1} {β : Type u_2} 
{β₂ : Type u_3} [inst : NormedAddCommGroup β] [inst_1 : Norm β₂] {l : Filter α} 
  {f g₁ : α → β} {g₂ : α → β…
-/
instance transIsEquivalentIsTheta :
    @Trans (α → β) (α → β) (α → β₂) (IsEquivalent l) (IsTheta l) (IsTheta l) where
  trans := IsEquivalent.trans_isTheta

@[trans]
/-
**Asymptotics.IsTheta.trans_isEquivalent** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsTheta`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {β₂ : Type u_3} [inst : NormedAddCommGroup
 β] [inst_1 : Norm β₂] {l : Filter α}   {f : α → β₂} {g₁ g₂ : α → β}, f =Θ[l] g₁
 → Asymptotics.IsEquivalent l g₁ g₂ → f =Θ[l] g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5
} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddCom
mGroup F'] {l :…
· 使用定理 `Asymptotics.IsEquivalent.isTheta`：∀ {α : Type u_1} {β : Type u_2} [inst 
: NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent
 l u v → u =Θ[l] v
-/
theorem IsTheta.trans_isEquivalent {f : α → β₂} {g₁ g₂ : α → β} (h : f =Θ[l] g₁)
    (h₂ : g₁ ~[l] g₂) : f =Θ[l] g₂ :=
  IsTheta.trans h h₂.isTheta
/-
**Asymptotics.transIsThetaIsEquivalent** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
形式化陈述：transIsThetaIsEquivalent : @Trans (α -> β₂) (α -> β) (α -> β) (IsTheta l) 
(IsEquivalent l) (IsTheta l) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.trans_isEquivalent`：∀ {α : Type u_1} {β : Type u_2} 
{β₂ : Type u_3} [inst : NormedAddCommGroup β] [inst_1 : Norm β₂] {l : Filter α} 
  {f : α → β₂} {g₁ g₂ : α → …
-/
instance transIsThetaIsEquivalent :
    @Trans (α → β₂) (α → β) (α → β) (IsTheta l) (IsEquivalent l) (IsTheta l) where
  trans := IsTheta.trans_isEquivalent
/-
**Asymptotics.IsEquivalent.comp_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.I
sEquivalent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {l : Filter 
α} {α₂ : Type u_4} {f g : α₂ → β}   {l' : Filter α₂},   Asymptotics.IsEquivalent
 l' f g → ∀ {k : α → α₂}, Filter.Tendsto k l l' → Asymptotics.IsEquivalent l (f 
∘ k) (g ∘ k)
参数：f ∘ k；g ∘ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E :
 Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α →
 F}   {l : Filter α}, f …
-/
theorem IsEquivalent.comp_tendsto {α₂ : Type*} {f g : α₂ → β} {l' : Filter α₂}
    (hfg : f ~[l'] g) {k : α → α₂} (hk : Filter.Tendsto k l l') : (f ∘ k) ~[l] (g ∘ k) :=
  IsLittleO.comp_tendsto hfg hk

@[simp]
/-
**Asymptotics.isEquivalent_map** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isEquivalent_map {α₂ : Type*} {f g : α₂ -> β} {k : α -> α₂} : f ~[Filter.m
ap k l] g ↔ (f ∘ k) ~[l] (g ∘ k)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_map`：isLittleO_map {k : β -> α} {l : Filter β} : f
 =o[map k l] g ↔ (f ∘ k) =o[l] (g ∘ k)
-/
theorem isEquivalent_map {α₂ : Type*} {f g : α₂ → β} {k : α → α₂} :
    f ~[Filter.map k l] g ↔ (f ∘ k) ~[l] (g ∘ k) :=
  isLittleO_map
/-
**Asymptotics.IsEquivalent.mono** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsEquival
ent`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : NormedAddCommGroup β] {l : Filter 
α} {f g : α → β} {l' : Filter α},   Asymptotics.IsEquivalent l' f g → l ≤ l' → A
symptotics.IsEquivalent l f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}
, f =o[l'] g → l…
-/
theorem IsEquivalent.mono {f g : α → β} {l' : Filter α} (h : f ~[l'] g) (hl : l ≤ l') :
    f ~[l] g :=
  IsLittleO.mono h hl

end Asymptotics

