/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Shifting an affine subspace towards a point

This file introduces a "shift" transformation of affine subspace, where the subspace is translated
relatively to a point `c`. This is equivalent to `AffineSubspace.map (AffineEquiv.constVAdd ..)`,
but hides the detail of arbitrarily choosing a point in the subspace.

Shifting is controlled by a parameter `r`, indicating how far the output space is to `c`. We set
`r = 0` to mean the output space passes through `c` (See `AffineSubspace.shift_zero`),
while `r = 1` means not moving the input space at all (See `AffineSubspace.shift_one`).
With this convention, this transformation is also equivalent to `AffineSubspace.map (homothety c r)`
when `r` is a unit.

## Main declarations
* `AffineSubspace.shift` defines the shift transformation.
* `AffineSubspace.shift_eq` shows the shift transformation is equivalent to translation.
* `AffineSubspace.shift_eq_map_homothety` shows the shift transformation is equivalent to homothety.
-/

public section

open Module Submodule Finset AffineMap AffineSubspace

variable {k V P : Type*}

namespace AffineSubspace

section Ring
variable [Ring k] [AddCommGroup V] [AddTorsor V P] [Module k V]

open scoped Classical in
/-- `AffineSubspace.shift s c r` is an affine subspace parallel to `s`, where an arbitrary point on
`s` is moved towards `c` with linear interpolation by `r`. When `r = 0`, that point is moved onto
`c`. When `r = 1`, that point stays at the original position. A different choice of the point will
not affect the output (See `AffineSubspace.shift_eq`).

We define `AffineSubspace.shift ⊥ c r = ⊥` (See `AffineSubspace.shift_bot`). -/
noncomputable
/-
**AffineSubspace.shift** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：shift (s : AffineSubspace k P) (c : P) (r : k) : AffineSubspace k P
参数：s : AffineSubspace k P；c : P；r : k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def shift (s : AffineSubspace k P) (c : P) (r : k) : AffineSubspace k P :=
  if h : Nonempty s then
    s.map <| AffineEquiv.constVAdd k P ((1 - r) • (c -ᵥ h.some))
  else
    ⊥

@[simp]
/-
**AffineSubspace.direction_shift** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：direction_shift (s : AffineSubspace k P) (c : P) (r : k) : (s.shift c r).d
irection = s.direction
参数：s : AffineSubspace k P；c : P；r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.eq_bot_or_nonempty`：eq_bot_or_nonempty (Q : AffineSubspac
e k P) : Q = ⊥ ∨ (Q : Set P).Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineSubspace.map_bot`：map_bot : (⊥ : AffineSubspace k P₁).map f = ⊥
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `AffineSubspace.direction_bot`：direction_bot : (⊥ : AffineSubspace k P).d
irection = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `AffineSubspace.map_direction`：map_direction (s : AffineSubspace k P₁) : 
(s.map f).direction = s.direction.map f.linear
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `AffineEquiv.linear_constVAdd`：∀ (k : Type u_1) (P₁ : Type u_2) {V₁ : Typ
e u_6} [inst : Ring k] [inst_1 : AddCommGroup V₁]   [inst_2 : _root_.Module k V₁
] [inst_3 : AddTor…
· 使用定理 `Submodule.map_id`：map_id : map (LinearMap.id : M ->ₗ[R] M) p = p
-/
theorem direction_shift (s : AffineSubspace k P) (c : P) (r : k) :
    (s.shift c r).direction = s.direction := by
  rcases s.eq_bot_or_nonempty with h | h
  · simp [shift, h]
  have h : Nonempty s := by simpa using! h
  simp [shift, h]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AffineSubspace.shift_top** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：shift_top (c : P) (r : k) : shift ⊤ c r = ⊤
参数：c : P；r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `AffineMap.map_top_of_surjective`：map_top_of_surjective (hf : Function.Su
rjective f) : AffineSubspace.map f ⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem shift_top (c : P) (r : k) : shift ⊤ c r = ⊤ := by
  simp [shift, AffineEquiv.surjective]

@[simp]
/-
**AffineSubspace.shift_bot** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：shift_bot (c : P) (r : k) : shift ⊥ c r = ⊥
参数：c : P；r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineSubspace.map_bot`：map_bot : (⊥ : AffineSubspace k P₁).map f = ⊥
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem shift_bot (c : P) (r : k) : shift ⊥ c r = ⊥ := by
  simp [shift]

/-- `AffineSubspace.shift s c r` can be represented by moving a point in the subspace
towards `c`. -/
/-
**AffineSubspace.shift_eq** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：shift_eq {s : AffineSubspace k P} (p : s) (c : P) (r : k) : s.shift c r = 
s.map (AffineEquiv.constVAdd k P ((1 - r) • (c -ᵥ p)))
参数：p : s；c : P；r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `AffineSubspace.ext`：ext {p q : AffineSubspace k P} (h : forall x, x in p
 ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineEquiv.constVAdd_apply`：∀ (k : Type u_1) (P₁ : Type u_2) {V₁ : Type
 u_6} [inst : Ring k] [inst_1 : AddCommGroup V₁]   [inst_2 : _root_.Module k V₁]
 [inst_3 : AddTor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.vadd_mem_of_mem_direction`：vadd_mem_of_mem_direction {s :
 AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} (hp : p in s) : v +
ᵥ p in s
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `vadd_vadd`：∀ {M : Type u_1} {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (a₁ a₂ : M) (b : α),   a₁ +ᵥ a₂ +ᵥ b = (a₁ + a₂) +ᵥ b
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃

--- 原说明 ---
`AffineSubspace.shift s c r` can be represented by moving a point in the subspac
e
towards `c`.
-/
theorem shift_eq {s : AffineSubspace k P} (p : s) (c : P) (r : k) :
    s.shift c r = s.map (AffineEquiv.constVAdd k P ((1 - r) • (c -ᵥ p))) := by
  have h : Nonempty s := ⟨p⟩
  simp only [shift, h, ↓reduceDIte]
  ext q
  simp only [mem_map, AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply]
  constructor <;> intro ⟨x, hx, heq⟩ <;> rw [← heq]
  · refine ⟨(1 - r) • (p.val -ᵥ h.some.val) +ᵥ x, ?_, ?_⟩
    · exact vadd_mem_of_mem_direction (smul_mem _ _ (vsub_mem_direction p.prop h.some.prop)) hx
    · rw [vadd_vadd, ← smul_add, vsub_add_vsub_cancel]
  · refine ⟨(1 - r) • (h.some.val -ᵥ p.val) +ᵥ x, ?_, ?_⟩
    · exact vadd_mem_of_mem_direction (smul_mem _ _ (vsub_mem_direction h.some.prop p.prop)) hx
    · rw [vadd_vadd, ← smul_add, vsub_add_vsub_cancel]

@[simp]
/-
**AffineSubspace.shift_zero** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：shift_zero (s : AffineSubspace k P) [h : Nonempty s] (c : P) : s.shift c 0
 = mk' c s.direction
参数：s : AffineSubspace k P；c : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.ext_of_direction_eq`：ext_of_direction_eq {s₁ s₂ : AffineS
ubspace k P} (hd : s₁.direction = s₂.direction) (hn : ((s₁ : Set P) inter s₂).No
nempty) : s₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.direction_shift`：direction_shift (s : AffineSubspace k P)
 (c : P) (r : k) : (s.shift c r).direction = s.direction
· 使用定理 `AffineSubspace.direction_mk'`：direction_mk' (p : P) (direction : Submodu
le k V) : (mk' p direction).direction = direction
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `AffineEquiv.constVAdd_apply`：∀ (k : Type u_1) (P₁ : Type u_2) {V₁ : Type
 u_6} [inst : Ring k] [inst_1 : AddCommGroup V₁]   [inst_2 : _root_.Module k V₁]
 [inst_3 : AddTor…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem shift_zero (s : AffineSubspace k P) [h : Nonempty s] (c : P) :
    s.shift c 0 = mk' c s.direction := by
  refine ext_of_direction_eq (by simp) ⟨c, ?_⟩
  suffices ∃ x ∈ s, (c -ᵥ h.some) +ᵥ x = c by simpa [shift, h]
  exact ⟨h.some, by simp⟩

@[simp]
/-
**AffineSubspace.shift_one** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：shift_one (s : AffineSubspace k P) (c : P) : s.shift c 1 = s
参数：s : AffineSubspace k P；c : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.eq_bot_or_nonempty`：eq_bot_or_nonempty (Q : AffineSubspac
e k P) : Q = ⊥ ∨ (Q : Set P).Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineSubspace.shift_bot`：shift_bot (c : P) (r : k) : shift ⊥ c r = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `AffineEquiv.constVAdd_zero`：constVAdd_zero : constVAdd k P₁ 0 = AffineEq
uiv.refl _ _
· 使用定理 `AffineSubspace.map_id`：map_id (s : AffineSubspace k P₁) : s.map (AffineM
ap.id k P₁) = s
-/
theorem shift_one (s : AffineSubspace k P) (c : P) : s.shift c 1 = s := by
  rcases s.eq_bot_or_nonempty with h | h
  · simp [h]
  have h : Nonempty s := by simpa using! h
  simp [shift, h]

/-- Consider a point `A` with barycentric coordinates associated to a collection of points `P`.
If the coordinate associated to one of the points `Pᵢ` is `r`, then the point `A` is on the span
of `P \ {Pᵢ}` shifted towards `Pᵢ` with parameter `1 - r`. -/
/-
**AffineSubspace.affineCombination_mem_shift** 是 Mathlib 中的一个定理，位于命名空间 `AffineSu
bspace`。
形式化陈述：affineCombination_mem_shift {ι : Type*} [Fintype ι] [Nontrivial ι] (p : ι 
-> P) (i : ι) {w : ι -> k} (hw : ∑ i, w i = 1) : affineCombination k univ p w in
 (affineSpan k <| p '' {i}ᶜ).shift (p i) (1 - w i)
参数：p : ι -> P；i : ι；hw : ∑ i, w i = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddTorsor.subsingleton_iff`：∀ (G : Type u_1) (P : Type u_2) [inst : AddG
roup G] [AddTorsor G P], Subsingleton G ↔ Subsingleton P
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.shift_top`：shift_top (c : P) (r : k) : shift ⊤ c r = ⊤
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `AffineSubspace.shift_eq`：shift_eq {s : AffineSubspace k P} (p : s) (c : 
P) (r : k) : s.shift c r = s.map (AffineEquiv.constVAdd k P ((1 - r) • (c -ᵥ p))
)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.affineCombination_piSingle`：affineCombination_piSingle [Decidable
Eq ι] (p : ι -> P) {i : ι} (hi : i in s) : s.affineCombination k p (Pi.single i 
1) = p i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.affineCombination_vsub`：affineCombination_vsub (w₁ w₂ : ι -> k) (
p : ι -> P) : s.affineCombination k p w₁ -ᵥ s.affineCombination k p w₂ = s.weigh
tedVSub p (w₁ - w₂)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.weightedVSub_vadd_affineCombination`：weightedVSub_vadd_affineComb
ination (w₁ w₂ : ι -> k) (p : ι -> P) : s.weightedVSub p w₁ +ᵥ s.affineCombinati
on k p w₂ = s.affineCombination …
· 使用引理 `affineCombination_mem_affineSpan_image`：affineCombination_mem_affineSpan
_image [Nontrivial k] {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 1) {s' : 
Set ι} (hs' : forall i in s,…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `Finset.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] [inst_1 : DecidableEq ι] (a : ι) (x : M) (s : Finset ι),   ∑ a' ∈ s, Pi.
single a x …
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
Consider a point `A` with barycentric coordinates associated to a collection of 
points `P`.
If the coordinate associated to one of the points `Pᵢ` is `r`, then the point `A
` is on the span
of `P \ {Pᵢ}` shifted towards `Pᵢ` with parameter `1 - r`.
-/
theorem affineCombination_mem_shift {ι : Type*} [Fintype ι] [Nontrivial ι]
    (p : ι → P) (i : ι) {w : ι → k} (hw : ∑ i, w i = 1) :
    affineCombination k univ p w ∈ (affineSpan k <| p '' {i}ᶜ).shift (p i) (1 - w i) := by
  cases subsingleton_or_nontrivial k
  · suffices (affineSpan k <| p '' {i}ᶜ) = ⊤ by simp [this]
    have : Subsingleton P := (AddTorsor.subsingleton_iff V P).mp <| Module.subsingleton k V
    simp
  classical
  obtain ⟨j, hj⟩ := exists_ne i
  rw [shift_eq ⟨p j, mem_affineSpan k <| Set.mem_image_of_mem _ hj⟩]
  suffices ∃ q ∈ affineSpan k (p '' {i}ᶜ), w i • (p i -ᵥ p j) +ᵥ q = affineCombination k univ p w by
    simpa
  refine ⟨-(w i • (p i -ᵥ p j)) +ᵥ affineCombination k univ p w, ?_, by simp⟩
  rw [← affineCombination_piSingle k _ p (mem_univ i),
    ← affineCombination_piSingle k _ p (mem_univ j), affineCombination_vsub, ← map_smul, ← map_neg,
    weightedVSub_vadd_affineCombination]
  refine affineCombination_mem_affineSpan_image ?_ (fun i' _ hi ↦ by aesop) _
  simp [sum_add_distrib, ← mul_sum, hw]

/-- The iff version of `affineCombination_mem_shift` for affine independent points. -/
/-
**AffineSubspace._root_.AffineIndependent.affineCombination_mem_shift_iff** 是 Ma
thlib 中的一个定理，位于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The iff version of `affineCombination_mem_shift` for affine independent points.
-/
theorem _root_.AffineIndependent.affineCombination_mem_shift_iff
    {ι : Type*} [Fintype ι] [Nontrivial ι] {p : ι → P}
    (h : AffineIndependent k p) (i : ι) {w : ι → k} (hw : ∑ i, w i = 1) (c : k) :
    affineCombination k univ p w ∈ (affineSpan k <| p '' {i}ᶜ).shift (p i) c ↔
    w i = 1 - c := by
  classical
  refine ⟨?_, fun h ↦ by simpa [h] using affineCombination_mem_shift p i hw⟩
  obtain ⟨j, hj⟩ := exists_ne i
  rw [shift_eq ⟨p j, mem_affineSpan k <| Set.mem_image_of_mem _ hj⟩]
  suffices ∀ q ∈ affineSpan k (p '' {i}ᶜ),
    (1 - c) • (p i -ᵥ p j) +ᵥ q = affineCombination k univ p w → w i = 1 - c by simpa
  intro q hqmem heq
  obtain ⟨t, w', ht, hw', rfl⟩ := eq_affineCombination_of_mem_affineSpan_image hqmem
  have ht : (t : Set ι).indicator w' i = 0 := Set.indicator_of_notMem (by simpa using ht) w'
  rw [affineCombination_indicator_subset _ _ t.subset_univ,
    ← affineCombination_piSingle k _ p (mem_univ i),
    ← affineCombination_piSingle k _ p (mem_univ j), affineCombination_vsub, ← map_smul,
    weightedVSub_vadd_affineCombination, h.affineCombination_eq_iff_eq ?_ hw] at heq
  · simpa [hj.symm, ht] using (heq i (mem_univ i)).symm
  · simp [sum_add_distrib, sum_indicator_subset, ← mul_sum, hw']

end Ring

section CommRing
variable [CommRing k] [AddCommGroup V] [AddTorsor V P] [Module k V]

/-- For a unit parameter, shifting is the same as mapping by homothety. -/
/-
**AffineSubspace.shift_eq_map_homothety** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e`。
形式化陈述：shift_eq_map_homothety (s : AffineSubspace k P) (c : P) {r : k} (hr : IsUn
it r) : s.shift c r = s.map (homothety c r)
参数：s : AffineSubspace k P；c : P；hr : IsUnit r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUnit.exists_right_inv`：IsUnit.exists_right_inv (h : IsUnit a) : exists
 b, a * b = 1
· 使用定理 `AffineSubspace.eq_bot_or_nonempty`：eq_bot_or_nonempty (Q : AffineSubspac
e k P) : Q = ⊥ ∨ (Q : Set P).Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineSubspace.shift_bot`：shift_bot (c : P) (r : k) : shift ⊥ c r = ⊥
· 使用定理 `AffineSubspace.map_bot`：map_bot : (⊥ : AffineSubspace k P₁).map f = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AffineSubspace.shift_eq`：shift_eq {s : AffineSubspace k P} (p : s) (c : 
P) (r : k) : s.shift c r = s.map (AffineEquiv.constVAdd k P ((1 - r) • (c -ᵥ p))
)
· 使用定理 `AffineSubspace.ext`：ext {p q : AffineSubspace k P} (h : forall x, x in p
 ↔ x in q) : p = q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.vadd_mem_of_mem_direction`：vadd_mem_of_mem_direction {s :
 AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} (hp : p in s) : v +
ᵥ p in s
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `vsub_vadd_comm`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCommGroup G] 
[inst_1 : AddTorsor G P] (p₁ p₂ p₃ : P),   (p₁ -ᵥ p₂) +ᵥ p₃ = (p₃ -ᵥ p₂) +ᵥ p₁
· 使用定理 `vadd_vadd`：∀ {M : Type u_1} {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (a₁ a₂ : M) (b : α),   a₁ +ᵥ a₂ +ᵥ b = (a₁ + a₂) +ᵥ b
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
For a unit parameter, shifting is the same as mapping by homothety.
-/
theorem shift_eq_map_homothety (s : AffineSubspace k P) (c : P) {r : k} (hr : IsUnit r) :
    s.shift c r = s.map (homothety c r) := by
  obtain ⟨t, ht⟩ := hr.exists_right_inv
  rcases s.eq_bot_or_nonempty with h | h
  · simp [h]
  have h : Nonempty s := by simpa using! h
  rw [s.shift_eq h.some]
  ext p
  suffices (∃ y ∈ s, (1 - r) • (c -ᵥ h.some) +ᵥ y = p) ↔ ∃ y ∈ s, r • (y -ᵥ c) +ᵥ c = p by
    simpa [homothety_def]
  constructor <;> intro ⟨x, hmem, heq⟩ <;> rw [← heq]
  · refine ⟨t • (x -ᵥ h.some.val) +ᵥ h.some.val, ?_, ?_⟩
    · refine vadd_mem_of_mem_direction ?_ h.some.prop
      exact smul_mem _ _ <| vsub_mem_direction hmem h.some.prop
    · rw [vadd_vsub_assoc, smul_add, smul_smul, ht, sub_eq_add_neg, add_smul, one_smul, one_smul,
        neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]
      simp_rw [add_comm _ (r • (h.some.val -ᵥ c)), ← vadd_vadd, vsub_vadd_comm x h.some.val c]
  · refine ⟨r • (x -ᵥ h.some.val) +ᵥ h.some.val, ?_, ?_⟩
    · refine vadd_mem_of_mem_direction ?_ h.some.prop
      exact smul_mem _ _ <| vsub_mem_direction hmem h.some.prop
    · rw [sub_eq_add_neg, add_smul, one_smul, neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev,
        ← vadd_vadd, vadd_vadd _ _ h.some.val, ← smul_add, add_comm, vsub_add_vsub_cancel,
        vadd_vadd, add_comm, ← vadd_vadd, vsub_vadd]

end CommRing

end AffineSubspace

namespace Affine.Simplex

section Ring
variable [Ring k] [PartialOrder k] [IsOrderedAddMonoid k] [AddCommGroup V] [AddTorsor V P]
  [Module k V] {n : ℕ} [NeZero n] (s : Affine.Simplex k P n) (i : Fin (n + 1))

/-- The base of a simplex shifted with parameter 0 intersects the closed interior only at the
vertex. -/
/-
**Affine.Simplex.closedInterior_inter_shift_zero** 是 Mathlib 中的一个定理，位于命名空间 `Affi
ne.Simplex`。
形式化陈述：closedInterior_inter_shift_zero [ZeroLEOneClass k] : s.closedInterior inte
r (affineSpan k <| s.points '' {i}ᶜ).shift (s.points i) 0 = {s.points i}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `eq_affineCombination_of_mem_affineSpan_of_fintype`：eq_affineCombination_
of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι -> P} (h : p1 in affine
Span k (Set.range p)) : exists w : ι ->…
· 使用引理 `Affine.Simplex.closedInterior_subset_affineSpan`：closedInterior_subset_a
ffineSpan {n : Nat} {s : Simplex k P n} : s.closedInterior subseteq affineSpan k
 (Set.range s.points)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `AffineIndependent.affineCombination_mem_shift_iff`：∀ {k : Type u_1} {V :
 Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : Ad
dTorsor V P]   [inst_3 : _root_.Module …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Finset.sum_eq_zero_iff_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst 
: AddCommMonoid N] [inst_1 : PartialOrder N] {f : ι → N} {s : Finset ι}   [AddLe
ftMono N], (∀ i ∈ s, 0…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Affine.Simplex.affineCombination_mem_closedInterior_iff`：affineCombinati
on_mem_closedInterior_iff {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -> k} (
hw : ∑ i, w i = 1) : Finset.univ.affineCombin…
· 使用定理 `add_eq_right`：∀ {M : Type u_4} [inst : AddMonoid M] [IsRightCancelAdd M]
 {a b : M}, a + b = b ↔ a = 0
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_erase_add`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → ∑ 
x ∈ s.eras…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
The base of a simplex shifted with parameter 0 intersects the closed interior on
ly at the
vertex.
-/
theorem closedInterior_inter_shift_zero [ZeroLEOneClass k] :
    s.closedInterior ∩ (affineSpan k <| s.points '' {i}ᶜ).shift (s.points i) 0 =
    {s.points i} := by
  refine subset_antisymm (fun p ⟨hp, hshift⟩ ↦ ?_) (by simp [s.point_mem_closedInterior i])
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype <|
    s.closedInterior_subset_affineSpan hp
  suffices w = Pi.single i 1 by simp [this]
  rw [affineCombination_mem_closedInterior_iff hw] at hp
  rw [SetLike.mem_coe, s.independent.affineCombination_mem_shift_iff i hw, sub_zero] at hshift
  ext j
  by_cases hj : j = i
  · aesop
  rw [← univ.sum_erase_add w (mem_univ i), hshift, add_eq_right,
    sum_eq_zero_iff_of_nonneg fun j _ ↦ (hp j).1] at hw
  simp [hw j (by simpa using hj), hj]

/-- The base of a simplex shifted with parameter outside $[0, 1]$ does not intersect the closed
interior. -/
/-
**Affine.Simplex.disjoint_closedInterior_shift** 是 Mathlib 中的一个定理，位于命名空间 `Affine
.Simplex`。
形式化陈述：disjoint_closedInterior_shift {x : k} (hx : x < 0 ∨ 1 < x) : Disjoint s.cl
osedInterior (affineSpan k (s.points '' {i}ᶜ)).shift (s.points i) x
参数：hx : x < 0 ∨ 1 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `eq_affineCombination_of_mem_affineSpan_of_fintype`：eq_affineCombination_
of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι -> P} (h : p1 in affine
Span k (Set.range p)) : exists w : ι ->…
· 使用引理 `Affine.Simplex.closedInterior_subset_affineSpan`：closedInterior_subset_a
ffineSpan {n : Nat} {s : Simplex k P n} : s.closedInterior subseteq affineSpan k
 (Set.range s.points)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.affineCombination_mem_closedInterior_iff`：affineCombinati
on_mem_closedInterior_iff {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -> k} (
hw : ∑ i, w i = 1) : Finset.univ.affineCombin…
· 使用定理 `AffineIndependent.affineCombination_mem_shift_iff`：∀ {k : Type u_1} {V :
 Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : Ad
dTorsor V P]   [inst_3 : _root_.Module …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The base of a simplex shifted with parameter outside $[0, 1]$ does not intersect
 the closed
interior.
-/
theorem disjoint_closedInterior_shift {x : k} (hx : x < 0 ∨ 1 < x) :
    Disjoint s.closedInterior <| (affineSpan k (s.points '' {i}ᶜ)).shift (s.points i) x := by
  refine Set.disjoint_left.mpr fun p hleft hright ↦ ?_
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype <|
    s.closedInterior_subset_affineSpan hleft
  rw [SetLike.mem_coe, s.independent.affineCombination_mem_shift_iff i hw] at hright
  rw [affineCombination_mem_closedInterior_iff hw] at hleft
  grind

end Ring

section Field
variable [Field k] [LinearOrder k] [IsOrderedRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/-
**Affine.Simplex.closedInterior_inter_shift_aux** 是 Mathlib 中的一个定理，位于命名空间 `Affin
e.Simplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem closedInterior_inter_shift_aux {n : ℕ} (i : Fin n) {x : k} (hxpos : 0 < x)
    (hx1 : x ≤ 1) {w : Fin n → k} (hw : ∑ i, w i = 1) :
    (∀ j, w j ∈ Set.Icc 0 1) ∧ w i = 1 - x ↔
    (∀ j, j ≠ i → x⁻¹ * w j ∈ Set.Icc 0 1) ∧ x⁻¹ * (w i - 1) + 1 = 0 := by
  rw [show x⁻¹ * (w i - 1) + 1 = 0 ↔ w i = 1 - x by grind]
  refine and_congr_left fun hi ↦ ⟨fun hj j hji ↦ ⟨?_, ?_⟩, fun hj ↦ ?_⟩
  · exact mul_nonneg (by simpa using hxpos.le) (hj j).1
  · rw [eq_sub_iff_add_eq, add_comm, ← eq_sub_iff_add_eq] at hi
    rw [inv_mul_le_one₀ hxpos, hi, le_sub_iff_add_le, ← hw]
    exact add_le_sum (fun i _ ↦ (hj i).1) (mem_univ j) (mem_univ i) hji
  · suffices ∀ j, 0 ≤ w j from
      fun j ↦ ⟨this j, hw ▸ Finset.single_le_sum (fun j _ ↦ this j) (mem_univ j)⟩
    intro j
    by_cases hji : j = i <;> aesop

set_option backward.isDefEq.respectTransparency.types false in
/-- A parallel cross-section of a simplex is the image of the base under a homothety. -/
/-
**Affine.Simplex.closedInterior_inter_shift_eq_homothety** 是 Mathlib 中的一个定理，位于命名
空间 `Affine.Simplex`。
形式化陈述：closedInterior_inter_shift_eq_homothety {n : Nat} [NeZero n] (s : Affine.S
implex k P n) (i : Fin (n + 1)) {x : k} (hx : x in Set.Icc 0 1) : s.closedInteri
or inter (affineSpan k (s.points '' {i}ᶜ)).shift (s.points i) x = homothety (s.p
oints i) x '' (s.faceOpposite i).closedInterior
参数：s : Affine.Simplex k P n；i : Fin (n + 1)；hx : x in Set.Icc 0 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.shift_zero`：shift_zero (s : AffineSubspace k P) [h : None
mpty s] (c : P) : s.shift c 0 = mk' c s.direction
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.instNonemptyElemImage`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (
s : Set α) [Nonempty ↑s], Nonempty ↑(f '' s)
· 使用定理 `Affine.Simplex.instNonemptyElemComplSetSingletonOfNontrivial`：∀ {α : Typ
e u_8} [Nontrivial α] (i : α), Nonempty ↑{i}ᶜ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineMap.homothety_zero`：homothety_zero (c : P1) : homothety c (0 : k) 
= const k P1 c
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Affine.Simplex.closedInterior_inter_shift_zero`：closedInterior_inter_shi
ft_zero [ZeroLEOneClass k] : s.closedInterior inter (affineSpan k <| s.points ''
 {i}ᶜ).shift (s.points i) 0 = {s.poi…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `eq_affineCombination_of_mem_affineSpan_of_fintype`：eq_affineCombination_
of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι -> P} (h : p1 in affine
Span k (Set.range p)) : exists w : ι ->…
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `AffineIndependent.affineCombination_mem_shift_iff`：∀ {k : Type u_1} {V :
 Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : Ad
dTorsor V P]   [inst_3 : _root_.Module …
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用引理 `Affine.Simplex.affineCombination_mem_closedInterior_iff`：affineCombinati
on_mem_closedInterior_iff {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -> k} (
hw : ∑ i, w i = 1) : Finset.univ.affineCombin…
（共 71 条，此处仅展示前 30 条）

--- 原说明 ---
A parallel cross-section of a simplex is the image of the base under a homothety
.
-/
theorem closedInterior_inter_shift_eq_homothety {n : ℕ} [NeZero n] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) {x : k} (hx : x ∈ Set.Icc 0 1) :
    s.closedInterior ∩ (affineSpan k (s.points '' {i}ᶜ)).shift (s.points i) x =
    homothety (s.points i) x '' (s.faceOpposite i).closedInterior := by
  rcases hx.1.eq_or_lt with hx0 | hxpos
  · simpa [hx0.symm, nonempty_closedInterior] using s.closedInterior_inter_shift_zero i
  ext p
  by_cases hp : p ∈ affineSpan k (.range s.points)
  · obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    rw [Set.mem_inter_iff, SetLike.mem_coe, s.independent.affineCombination_mem_shift_iff i hw,
      affineCombination_mem_closedInterior_iff hw, Set.mem_image]
    simp_rw [AffineMap.homothety_eq_iff_of_mul_eq_one (mul_inv_cancel₀ hxpos.ne.symm),
      univ.homothety_affineCombination _ _ (mem_univ i)]
    simp only [↓existsAndEq, and_true]
    rw [faceOpposite, affineCombination_mem_closedInterior_face_iff_mem_Icc,
      closedInterior_inter_shift_aux i hxpos hx.2 hw]
    · simp only [mem_compl, mem_singleton, not_not, forall_eq]
      congrm (∀ j, (hj : _) → $(by simp [lineMap_apply, hj])) ∧ $(by simp [lineMap_apply])
    · simp [AffineMap.lineMap_apply, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_sub_distrib, hw]
  · apply iff_of_false (hp <| s.closedInterior_subset_affineSpan ·.1)
    rintro ⟨q, hq, rfl⟩
    exact hp <| homothety_mem (mem_affineSpan _ (by simp)) _ <|
      affineSpan_mono _ (by simp) ((s.faceOpposite i).closedInterior_subset_affineSpan hq)

end Field
end Affine.Simplex

