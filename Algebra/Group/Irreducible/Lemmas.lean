/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# More lemmas about irreducible elements
-/

public section

assert_not_exists MonoidWithZero IsOrderedMonoid Multiset

variable {F M N : Type*}

section Monoid
variable [Monoid M] [Monoid N] {f : F} {x y : M}

@[to_additive]
/-
**not_irreducible_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_irreducible_pow : forall {n : Nat}, n != 1 -> ¬ Irreducible (x ^ n) | 
0, _ => by simp | n + 2, _ => by intro ⟨h₁, h₂⟩ have
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `isUnit_pow_iff`：∀ {M : Type u_1} [inst : Monoid M] {n : ℕ} {a : M}, n ≠ 
0 → (IsUnit (a ^ n) ↔ IsUnit a)
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
-/
lemma not_irreducible_pow : ∀ {n : ℕ}, n ≠ 1 → ¬ Irreducible (x ^ n)
  | 0, _ => by simp
  | n + 2, _ => by
    intro ⟨h₁, h₂⟩
    have := h₂ (pow_succ _ _)
    rw [isUnit_pow_iff n.succ_ne_zero, or_self] at this
    exact h₁ (this.pow _)

@[to_additive]
/-
**irreducible_units_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：irreducible_units_mul (u : Mˣ) : Irreducible (u * y) ↔ Irreducible y
参数：u : Mˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.isUnit_units_mul`：Units.isUnit_units_mul {M : Type*} [Monoid M] (u
 : Mˣ) (a : M) : IsUnit (↑u * a) ↔ IsUnit a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Units.inv_mul_cancel_left`：inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ 
: α) * (a * b) = b
-/
lemma irreducible_units_mul (u : Mˣ) : Irreducible (u * y) ↔ Irreducible y := by
  simp only [irreducible_iff, Units.isUnit_units_mul, and_congr_right_iff]
  refine fun _ => ⟨fun h A B HAB => ?_, fun h A B HAB => ?_⟩
  · rw [← u.isUnit_units_mul]
    apply h
    rw [mul_assoc, ← HAB]
  · rw [← u⁻¹.isUnit_units_mul]
    apply h
    rw [mul_assoc, ← HAB, Units.inv_mul_cancel_left]

@[to_additive]
/-
**irreducible_isUnit_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：irreducible_isUnit_mul (h : IsUnit x) : Irreducible (x * y) ↔ Irreducible 
y
参数：h : IsUnit x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `irreducible_units_mul`：irreducible_units_mul (u : Mˣ) : Irreducible (u *
 y) ↔ Irreducible y
-/
lemma irreducible_isUnit_mul (h : IsUnit x) : Irreducible (x * y) ↔ Irreducible y :=
  let ⟨x, ha⟩ := h
  ha ▸ irreducible_units_mul x

@[to_additive]
/-
**irreducible_mul_units** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：irreducible_mul_units (u : Mˣ) : Irreducible (y * u) ↔ Irreducible y
参数：u : Mˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.isUnit_mul_units`：Units.isUnit_mul_units [Monoid M] (a : M) (u : M
ˣ) : IsUnit (a * u) ↔ IsUnit a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Units.mul_inv_cancel_right`：mul_inv_cancel_right (a : α) (b : αˣ) : a * 
b * ↑b⁻¹ = a
-/
lemma irreducible_mul_units (u : Mˣ) : Irreducible (y * u) ↔ Irreducible y := by
  simp only [irreducible_iff, Units.isUnit_mul_units, and_congr_right_iff]
  refine fun _ => ⟨fun h A B HAB => ?_, fun h A B HAB => ?_⟩
  · rw [← u.isUnit_mul_units B]
    apply h
    rw [← mul_assoc, ← HAB]
  · rw [← u⁻¹.isUnit_mul_units B]
    apply h
    rw [← mul_assoc, ← HAB, Units.mul_inv_cancel_right]

@[to_additive]
/-
**irreducible_mul_isUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：irreducible_mul_isUnit (h : IsUnit x) : Irreducible (y * x) ↔ Irreducible 
y
参数：h : IsUnit x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `irreducible_mul_units`：irreducible_mul_units (u : Mˣ) : Irreducible (y *
 u) ↔ Irreducible y
-/
lemma irreducible_mul_isUnit (h : IsUnit x) : Irreducible (y * x) ↔ Irreducible y :=
  let ⟨x, hx⟩ := h
  hx ▸ irreducible_mul_units x

@[to_additive]
/-
**irreducible_mul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：irreducible_mul_iff : Irreducible (x * y) ↔ Irreducible x ∧ IsUnit y ∨ Irr
educible y ∧ IsUnit x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `irreducible_mul_isUnit`：irreducible_mul_isUnit (h : IsUnit x) : Irreduci
ble (y * x) ↔ Irreducible y
· 使用引理 `irreducible_isUnit_mul`：irreducible_isUnit_mul (h : IsUnit x) : Irreduci
ble (x * y) ↔ Irreducible y
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
-/
lemma irreducible_mul_iff :
    Irreducible (x * y) ↔ Irreducible x ∧ IsUnit y ∨ Irreducible y ∧ IsUnit x := by
  constructor
  · refine fun h => Or.imp (fun h' => ⟨?_, h'⟩) (fun h' => ⟨?_, h'⟩) (h.isUnit_or_isUnit rfl).symm
    · rwa [irreducible_mul_isUnit h'] at h
    · rwa [irreducible_isUnit_mul h'] at h
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
    · rwa [irreducible_mul_isUnit hb]
    · rwa [irreducible_isUnit_mul ha]

section MulEquivClass
variable [EquivLike F M N] [MulEquivClass F M N] (f : F)

@[to_additive]
/-
**MulEquiv.irreducible_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulEquiv.irreducible_iff : Irreducible (f x) ↔ Irreducible x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma MulEquiv.irreducible_iff : Irreducible (f x) ↔ Irreducible x := by
  simp [_root_.irreducible_iff, (EquivLike.surjective f).forall, ← map_mul, -isUnit_map_iff]

/-- Irreducibility is preserved by multiplicative equivalences.

Note that surjective + local hom is not enough. Consider the additive monoids `M = ℕ ⊕ ℕ`, `N = ℕ`,
with x surjective local (additive) hom `f : M →+ N` sending `(m, n)` to `2m + n`.
It is local because the only add unit in `N` is `0`, with preimage `{(0, 0)}` also an add unit.
Then `x = (1, 0)` is irreducible in `M`, but `f x = 2 = 1 + 1` is not irreducible in `N`. -/
@[to_additive /-- Irreducibility is preserved by additive equivalences. -/]
alias ⟨_, Irreducible.map⟩ := MulEquiv.irreducible_iff

end MulEquivClass

/-
**Irreducible.of_map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Irreducible.of_map [FunLike F M N] [MonoidHomClass F M N] [IsLocalHom f] (
hfx : Irreducible (f x)) : Irreducible x where not_isUnit hu
参数：hfx : Irreducible (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `IsUnit.of_map`：IsUnit.of_map (f : F) [IsLocalHom f] (a : R) (h : IsUnit 
(f a)) : IsUnit a
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Irreducible.of_map [FunLike F M N] [MonoidHomClass F M N] [IsLocalHom f]
    (hfx : Irreducible (f x)) : Irreducible x where
  not_isUnit hu := hfx.not_isUnit <| hu.map f
  isUnit_or_isUnit := by
    rintro p q rfl; exact (hfx.isUnit_or_isUnit <| map_mul f p q).imp (.of_map f _) (.of_map f _)

@[to_additive]
/-
**Irreducible.not_isSquare** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Irreducible.not_isSquare (ha : Irreducible x) : ¬IsSquare x
参数：ha : Irreducible x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isSquare_iff_exists_sq`：isSquare_iff_exists_sq (a : α) : IsSquare a ↔ ex
ists r, a = r ^ 2
· 使用引理 `not_irreducible_pow`：not_irreducible_pow : forall {n : Nat}, n != 1 -> ¬
 Irreducible (x ^ n) | 0, _ => by simp | n + 2, _ => by intro ⟨h₁, h₂⟩ have
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Irreducible.not_isSquare (ha : Irreducible x) : ¬IsSquare x := by
  rw [isSquare_iff_exists_sq]
  rintro ⟨y, rfl⟩
  exact not_irreducible_pow (by decide) ha

@[to_additive]
/-
**IsSquare.not_irreducible** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSquare.not_irreducible (ha : IsSquare x) : ¬Irreducible x
参数：ha : IsSquare x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Irreducible.not_isSquare`：Irreducible.not_isSquare (ha : Irreducible x) 
: ¬IsSquare x
-/
lemma IsSquare.not_irreducible (ha : IsSquare x) : ¬Irreducible x := fun h => h.not_isSquare ha

end Monoid

