/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
module

public import Mathlib.Algebra.Divisibility.Hom
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Ring.Defs

/-!
# Lemmas about divisibility in rings

Note that this file is imported by basic tactics like `linarith` and so must have only minimal
imports. Further results about divisibility in rings may be found in
`Mathlib/Algebra/Ring/Divisibility/Lemmas.lean` which is not subject to this import constraint.
-/

@[expose] public section


variable {α β : Type*}

section Semigroup

variable [Semigroup α] [Semigroup β] {F : Type*} [EquivLike F α β] [MulEquivClass F α β]

/-
**map_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_dvd_iff (f : F) {a b} : f a ∣ f b ↔ a ∣ b
参数：f : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem map_dvd_iff (f : F) {a b} : f a ∣ f b ↔ a ∣ b :=
  let f := MulEquivClass.toMulEquiv f
  ⟨fun h ↦ by rw [← f.left_inv a, ← f.left_inv b]; exact map_dvd f.symm h, map_dvd f⟩
/-
**map_dvd_iff_dvd_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_dvd_iff_dvd_symm (f : F) {a : α} {b : β} : f a ∣ b ↔ a ∣ (MulEquivClas
s.toMulEquiv f).symm b
参数：f : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquivClass.coe_symm_apply_apply`：∀ {α : Type u_9} {β : Type u_10} [in
st : Mul α] [inst_1 : Mul β] {F : Type u_11} [inst_2 : EquivLike F α β]   [inst_
3 : MulEquivClass F α β]…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_dvd_iff_dvd_symm (f : F) {a : α} {b : β} :
    f a ∣ b ↔ a ∣ (MulEquivClass.toMulEquiv f).symm b := by
  obtain ⟨c, rfl⟩ : ∃ c, f c = b := EquivLike.surjective f b
  simp [map_dvd_iff]
/-
**MulEquiv.decompositionMonoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulEquiv.decompositionMonoid (f : F) [DecompositionMonoid β] : Decompositi
onMonoid α where primal a b c h
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DecompositionMonoid.primal`：∀ {α : Type u_1} {inst : Semigroup α} [self 
: DecompositionMonoid α] (a : α), IsPrimal a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_dvd_iff`：map_dvd_iff (f : F) {a b} : f a ∣ f b ↔ a ∣ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EquivLike.apply_inv_apply`：apply_inv_apply (e : E) (b : β) : e (inv e b)
 = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `EquivLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : E) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem MulEquiv.decompositionMonoid (f : F) [DecompositionMonoid β] : DecompositionMonoid α where
  primal a b c h := by
    rw [← map_dvd_iff f, map_mul] at h
    obtain ⟨a₁, a₂, h⟩ := DecompositionMonoid.primal _ h
    refine ⟨EquivLike.inv f a₁, EquivLike.inv f a₂, ?_⟩
    simp_rw [← map_dvd_iff f, EquivLike.apply_inv_apply, h, true_and, ← EquivLike.apply_eq_iff_eq f,
      h.2.2, map_mul, EquivLike.apply_inv_apply]

/--
If `G` is a `LeftCancelSemiGroup`, left multiplication by `g` yields an equivalence between `G`
and the set of elements of `G` divisible by `g`.
-/
/-
**Equiv.dvd** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{G : Type u_4} → [inst : LeftCancelSemigroup G] → (g : G) → G ≃ { a // g ∣
 a }
参数：g : G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is a `LeftCancelSemiGroup`, left multiplication by `g` yields an equivale
nce between `G`
and the set of elements of `G` divisible by `g`.
-/
protected noncomputable def Equiv.dvd {G : Type*} [LeftCancelSemigroup G] (g : G) :
    G ≃ {a : G // g ∣ a} where
  toFun := fun a ↦ ⟨g * a, ⟨a, rfl⟩⟩
  invFun := fun ⟨_, h⟩ ↦ h.choose
  left_inv := fun _ ↦ by simp
  right_inv := by
    rintro ⟨_, ⟨_, rfl⟩⟩
    simp

@[simp]
/-
**Equiv.dvd_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.dvd_apply {G : Type*} [LeftCancelSemigroup G] (g a : G) : Equiv.dvd 
g a = g * a
参数：g a : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Equiv.dvd_apply {G : Type*} [LeftCancelSemigroup G] (g a : G) :
    Equiv.dvd g a = g * a := rfl

end Semigroup

section DistribSemigroup

variable [Add α] [Semigroup α]

/-
**dvd_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b
 + c
参数：h₁ : a ∣ b；h₂ : a ∣ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.elim`：Dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : forall c, b =
 a * c -> P) : P
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
  Dvd.elim h₁ fun d hd => Dvd.elim h₂ fun e he => Dvd.intro (d + e) (by simp [left_distrib, hd, he])

alias Dvd.dvd.add := dvd_add

end DistribSemigroup

section Semiring
variable [Semiring α] {a b c : α} {m n : ℕ}

/-
**min_pow_dvd_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：min_pow_dvd_add (ha : c ^ m ∣ a) (hb : c ^ n ∣ b) : c ^ min m n ∣ a + b
参数：ha : c ^ m ∣ a；hb : c ^ n ∣ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Semigroup α] [Lef
tDistribClass α] {a b c : α}, a ∣ b → a ∣ c → a ∣ b + c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `Nat.min_le_left`：∀ (a b : ℕ), min a b ≤ a
· 使用定理 `Nat.min_le_right`：∀ (a b : ℕ), min a b ≤ b
-/
lemma min_pow_dvd_add (ha : c ^ m ∣ a) (hb : c ^ n ∣ b) : c ^ min m n ∣ a + b :=
  ((pow_dvd_pow c (m.min_le_left n)).trans ha).add ((pow_dvd_pow c (m.min_le_right n)).trans hb)

end Semiring

section NonUnitalCommSemiring

variable [NonUnitalCommSemiring α]

/-
**Dvd.dvd.linear_comb** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dvd.dvd.linear_comb {d x y : α} (hdx : d ∣ x) (hdy : d ∣ y) (a b : α) : d 
∣ a * x + b * y
参数：hdx : d ∣ x；hdy : d ∣ y；a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Dvd.dvd.mul_left`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α}, a
 ∣ b → ∀ (c : α), a ∣ c * b
-/
theorem Dvd.dvd.linear_comb {d x y : α} (hdx : d ∣ x) (hdy : d ∣ y) (a b : α) : d ∣ a * x + b * y :=
  dvd_add (hdx.mul_left a) (hdy.mul_left b)

end NonUnitalCommSemiring

section Semigroup

variable [Semigroup α] [HasDistribNeg α] {a b : α}

/-- An element `a` of a semigroup with a distributive negation divides the negation of an element
`b` iff `a` divides `b`. -/
@[simp]
/-
**dvd_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_neg : a ∣ -b ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An element `a` of a semigroup with a distributive negation divides the negation 
of an element
`b` iff `a` divides `b`.
-/
theorem dvd_neg : a ∣ -b ↔ a ∣ b :=
  (Equiv.neg _).exists_congr_left.trans <| by
    simp only [Equiv.neg_symm, Equiv.neg_apply, mul_neg, neg_inj, Dvd.dvd]

/-- The negation of an element `a` of a semigroup with a distributive negation divides another
element `b` iff `a` divides `b`. -/
@[simp]
/-
**neg_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_dvd : -a ∣ b ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The negation of an element `a` of a semigroup with a distributive negation divid
es another
element `b` iff `a` divides `b`.
-/
theorem neg_dvd : -a ∣ b ↔ a ∣ b :=
  (Equiv.neg _).exists_congr_left.trans <| by
    simp only [Equiv.neg_symm, Equiv.neg_apply, mul_neg, neg_mul, neg_neg, Dvd.dvd]

alias ⟨Dvd.dvd.of_neg_left, Dvd.dvd.neg_left⟩ := neg_dvd

alias ⟨Dvd.dvd.of_neg_right, Dvd.dvd.neg_right⟩ := dvd_neg

end Semigroup

section NonUnitalRing

variable [NonUnitalRing α] {a b c : α}

/-
**dvd_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c
参数：h₁ : a ∣ b；h₂ : a ∣ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dvd.dvd.add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Semigroup α] [Lef
tDistribClass α] {a b c : α}, a ∣ b → a ∣ c → a ∣ b + c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Dvd.dvd.neg_right`：∀ {α : Type u_1} [inst : Semigroup α] [inst_1 : HasDi
stribNeg α] {a b : α}, a ∣ b → a ∣ -b
-/
theorem dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c := by
  simpa only [← sub_eq_add_neg] using h₁.add h₂.neg_right

alias Dvd.dvd.sub := dvd_sub

/-- If an element `a` divides another element `c` in a ring, `a` divides the sum of another element
`b` with `c` iff `a` divides `b`. -/
/-
**dvd_add_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b
参数：h : a ∣ c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `dvd_sub`：dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R

--- 原说明 ---
If an element `a` divides another element `c` in a ring, `a` divides the sum of 
another element
`b` with `c` iff `a` divides `b`.
-/
theorem dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
  ⟨fun H => by simpa only [add_sub_cancel_right] using dvd_sub H h, fun h₂ => dvd_add h₂ h⟩

/-- If an element `a` divides another element `b` in a ring, `a` divides the sum of `b` and another
element `c` iff `a` divides `c`. -/
/-
**dvd_add_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c
参数：h : a ∣ b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `dvd_add_left`：dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b

--- 原说明 ---
If an element `a` divides another element `b` in a ring, `a` divides the sum of 
`b` and another
element `c` iff `a` divides `c`.
-/
theorem dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c := by rw [add_comm]; exact dvd_add_left h

/-- If an element `a` divides another element `c` in a ring, `a` divides the difference of another
element `b` with `c` iff `a` divides `b`. -/
/-
**dvd_sub_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_sub_left (h : a ∣ c) : a ∣ b - c ↔ a ∣ b
参数：h : a ∣ c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dvd_add_left`：dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dvd_neg`：dvd_neg : a ∣ -b ↔ a ∣ b

--- 原说明 ---
If an element `a` divides another element `c` in a ring, `a` divides the differe
nce of another
element `b` with `c` iff `a` divides `b`.
-/
theorem dvd_sub_left (h : a ∣ c) : a ∣ b - c ↔ a ∣ b := by
  simpa only [← sub_eq_add_neg] using dvd_add_left (dvd_neg.2 h)

/-- If an element `a` divides another element `b` in a ring, `a` divides the difference of `b` and
another element `c` iff `a` divides `c`. -/
/-
**dvd_sub_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_sub_right (h : a ∣ b) : a ∣ b - c ↔ a ∣ c
参数：h : a ∣ b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `dvd_add_right`：dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c
· 使用定理 `dvd_neg`：dvd_neg : a ∣ -b ↔ a ∣ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If an element `a` divides another element `b` in a ring, `a` divides the differe
nce of `b` and
another element `c` iff `a` divides `c`.
-/
theorem dvd_sub_right (h : a ∣ b) : a ∣ b - c ↔ a ∣ c := by
  rw [sub_eq_add_neg, dvd_add_right h, dvd_neg]
/-
**dvd_iff_dvd_of_dvd_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_iff_dvd_of_dvd_sub (h : a ∣ b - c) : a ∣ b ↔ a ∣ c
参数：h : a ∣ b - c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `dvd_add_right`：dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dvd_iff_dvd_of_dvd_sub (h : a ∣ b - c) : a ∣ b ↔ a ∣ c := by
  rw [← sub_add_cancel b c, dvd_add_right h]
/-
**dvd_sub_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_sub_comm : a ∣ b - c ↔ a ∣ c - b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvd_neg`：dvd_neg : a ∣ -b ↔ a ∣ b
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dvd_sub_comm : a ∣ b - c ↔ a ∣ c - b := by rw [← dvd_neg, neg_sub]

end NonUnitalRing

section Ring

variable [Ring α] {a b : α}

/-- An element a divides the sum a + b if and only if a divides b. -/
@[simp]
/-
**dvd_add_self_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_add_self_left {a b : α} : a ∣ a + b ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_add_right`：dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a

--- 原说明 ---
An element a divides the sum a + b if and only if a divides b.
-/
theorem dvd_add_self_left {a b : α} : a ∣ a + b ↔ a ∣ b :=
  dvd_add_right (dvd_refl a)

/-- An element a divides the sum b + a if and only if a divides b. -/
@[simp]
/-
**dvd_add_self_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_add_self_right {a b : α} : a ∣ b + a ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_add_left`：dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a

--- 原说明 ---
An element a divides the sum b + a if and only if a divides b.
-/
theorem dvd_add_self_right {a b : α} : a ∣ b + a ↔ a ∣ b :=
  dvd_add_left (dvd_refl a)

/-- An element `a` divides the difference `a - b` if and only if `a` divides `b`. -/
@[simp]
/-
**dvd_sub_self_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_sub_self_left : a ∣ a - b ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_sub_right`：dvd_sub_right (h : a ∣ b) : a ∣ b - c ↔ a ∣ c
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a

--- 原说明 ---
An element `a` divides the difference `a - b` if and only if `a` divides `b`.
-/
theorem dvd_sub_self_left : a ∣ a - b ↔ a ∣ b :=
  dvd_sub_right dvd_rfl

/-- An element `a` divides the difference `b - a` if and only if `a` divides `b`. -/
@[simp]
/-
**dvd_sub_self_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_sub_self_right : a ∣ b - a ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_sub_left`：dvd_sub_left (h : a ∣ c) : a ∣ b - c ↔ a ∣ b
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a

--- 原说明 ---
An element `a` divides the difference `b - a` if and only if `a` divides `b`.
-/
theorem dvd_sub_self_right : a ∣ b - a ↔ a ∣ b :=
  dvd_sub_left dvd_rfl

end Ring

section NonUnitalCommRing

variable [NonUnitalCommRing α]

/-
**dvd_mul_sub_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_mul_sub_mul {k a b x y : α} (hab : k ∣ a - b) (hxy : k ∣ x - y) : k ∣ 
a * x - b * y
参数：hab : k ∣ a - b；hxy : k ∣ x - y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub_left_distrib`：mul_sub_left_distrib (a b c : α) : a * (b - c) = a
 * b - a * c
· 使用定理 `mul_sub_right_distrib`：mul_sub_right_distrib (a b c : α) : (a - b) * c =
 a * c - b * c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Dvd.dvd.mul_left`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α}, a
 ∣ b → ∀ (c : α), a ∣ c * b
· 使用定理 `Dvd.dvd.mul_right`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α}, a ∣ 
b → ∀ (c : α), a ∣ b * c
-/
theorem dvd_mul_sub_mul {k a b x y : α} (hab : k ∣ a - b) (hxy : k ∣ x - y) :
    k ∣ a * x - b * y := by
  convert dvd_add (hxy.mul_left a) (hab.mul_right y)
  rw [mul_sub_left_distrib, mul_sub_right_distrib]
  simp only [sub_eq_add_neg, add_assoc, neg_add_cancel_left]

end NonUnitalCommRing

