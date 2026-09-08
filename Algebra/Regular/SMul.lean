/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Push

/-!
# Action of regular elements on a module

We introduce `M`-regular elements, in the context of an `R`-module `M`.  The corresponding
predicate is called `IsSMulRegular`.

There are very limited typeclass assumptions on `R` and `M`, but the "mathematical" case of interest
is a commutative ring `R` acting on a module `M`. Since the properties are "multiplicative", there
is no actual requirement of having an addition, but there is a zero in both `R` and `M`.
Scalar multiplications involving `0` are, of course, all trivial.

The defining property is that an element `a ∈ R` is `M`-regular if the scalar multiplication map
`M → M`, defined by `m ↦ a • m`, is injective.

This property is the direct generalization to modules of the property `IsLeftRegular` defined in
`Algebra/Regular`.  Lemma `isLeftRegular_iff` shows that indeed the two notions
coincide.
-/

@[expose] public section


variable {R S : Type*} (M : Type*) {a b : R} {s : S}

/-- An `M`-regular element is an element `c` such that multiplication on the left by `c` is an
injective map `M → M`. -/
/-
**IsSMulRegular** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsSMulRegular [SMul R M] (c : R)
参数：c : R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `M`-regular element is an element `c` such that multiplication on the left by
 `c` is an
injective map `M → M`.
-/
def IsSMulRegular [SMul R M] (c : R) :=
  Function.Injective ((c • ·) : M → M)
/-
**IsLeftRegular.isSMulRegular** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeftRegular.isSMulRegular [Mul R] {c : R} (h : IsLeftRegular c) : IsSMul
Regular R c
参数：h : IsLeftRegular c。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsLeftRegular.isSMulRegular [Mul R] {c : R} (h : IsLeftRegular c) : IsSMulRegular R c :=
  h

/-- Left-regular multiplication on `R` is equivalent to `R`-regularity of `R` itself. -/
/-
**isLeftRegular_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLeftRegular_iff [Mul R] {a : R} : IsLeftRegular a ↔ IsSMulRegular R a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Left-regular multiplication on `R` is equivalent to `R`-regularity of `R` itself
.
-/
theorem isLeftRegular_iff [Mul R] {a : R} : IsLeftRegular a ↔ IsSMulRegular R a :=
  Iff.rfl
/-
**IsRightRegular.isSMulRegular** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRightRegular.isSMulRegular [Mul R] {c : R} (h : IsRightRegular c) : IsSM
ulRegular R (MulOpposite.op c)
参数：h : IsRightRegular c。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsRightRegular.isSMulRegular [Mul R] {c : R} (h : IsRightRegular c) :
    IsSMulRegular R (MulOpposite.op c) :=
  h

/-- Right-regular multiplication on `R` is equivalent to `Rᵐᵒᵖ`-regularity of `R` itself. -/
/-
**isRightRegular_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRightRegular_iff [Mul R] {a : R} : IsRightRegular a ↔ IsSMulRegular R (M
ulOpposite.op a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Right-regular multiplication on `R` is equivalent to `Rᵐᵒᵖ`-regularity of `R` it
self.
-/
theorem isRightRegular_iff [Mul R] {a : R} :
    IsRightRegular a ↔ IsSMulRegular R (MulOpposite.op a) :=
  Iff.rfl

variable {M}
/-
**isSMulRegular_map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSMulRegular_map [SMul R M] [SMul S M] (f : R -> S) (smul : forall m : M,
 f a • m = a • m) : IsSMulRegular M (f a) ↔ IsSMulRegular M a
参数：f : R -> S；smul : forall m : M, f a • m = a • m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isSMulRegular_map [SMul R M] [SMul S M] (f : R → S) (smul : ∀ m : M, f a • m = a • m) :
    IsSMulRegular M (f a) ↔ IsSMulRegular M a := by simp [IsSMulRegular, smul]

protected alias ⟨IsSMulRegular.of_map, IsSMulRegular.map⟩ := isSMulRegular_map

namespace IsSMulRegular

/-
**IsSMulRegular.natAbs_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：∀ {M : Type u_3} [inst : SubtractionMonoid M] {n : ℤ}, IsSMulRegular M n.n
atAbs ↔ IsSMulRegular M n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.sign_mul_natAbs`：∀ (a : ℤ), a.sign * ↑a.natAbs = a
· 使用定理 `Int.sign_trichotomy`：∀ (a : ℤ), a.sign = 1 ∨ a.sign = 0 ∨ a.sign = -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.one_mul`：∀ (a : ℤ), 1 * a = a
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.sign_eq_zero_iff_zero`：∀ {a : ℤ}, a.sign = 0 ↔ a = 0
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Int.mul_zero`：∀ (a : ℤ), a * 0 = 0
· 使用定理 `zero_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 • a = 0
· 使用定理 `Int.neg_one_mul`：∀ (a : ℤ), -1 * a = -a
· 使用定理 `neg_zsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ)
, -n • a = -(n • a)
-/
@[simp] theorem natAbs_iff [SubtractionMonoid M] {n : ℤ} :
    IsSMulRegular M n.natAbs ↔ IsSMulRegular M n := by
  simp_rw [IsSMulRegular, Function.Injective]
  conv_rhs => rw [← n.sign_mul_natAbs]
  obtain h | h | h := n.sign_trichotomy
  · simp [h]
  · simp [Int.sign_eq_zero_iff_zero.mp h]
  · simp [h, neg_zsmul]

section SMul

variable [SMul R M] [SMul R S] [SMul S M] [IsScalarTower R S M]

/-- The product of `M`-regular elements is `M`-regular. -/
/-
**IsSMulRegular.smul** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：smul (ra : IsSMulRegular M a) (rs : IsSMulRegular M s) : IsSMulRegular M (
a • s)
参数：ra : IsSMulRegular M a；rs : IsSMulRegular M s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z

--- 原说明 ---
The product of `M`-regular elements is `M`-regular.
-/
theorem smul (ra : IsSMulRegular M a) (rs : IsSMulRegular M s) : IsSMulRegular M (a • s) :=
  fun _ _ ab => rs (ra ((smul_assoc _ _ _).symm.trans (ab.trans (smul_assoc _ _ _))))

/-- If an element `b` becomes `M`-regular after multiplying it on the left by an `M`-regular
element, then `b` is `M`-regular. -/
/-
**IsSMulRegular.of_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：of_smul (a : R) (ab : IsSMulRegular M (a • s)) : IsSMulRegular M s
参数：a : R；ab : IsSMulRegular M (a • s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z

--- 原说明 ---
If an element `b` becomes `M`-regular after multiplying it on the left by an `M`
-regular
element, then `b` is `M`-regular.
-/
theorem of_smul (a : R) (ab : IsSMulRegular M (a • s)) : IsSMulRegular M s :=
  @Function.Injective.of_comp _ _ _ (fun m : M => a • m) _ fun c d cd => by
  dsimp only [Function.comp_def] at cd
  rw [← smul_assoc, ← smul_assoc] at cd
  exact ab cd

/-- An element is `M`-regular if and only if multiplying it on the left by an `M`-regular element
is `M`-regular. -/
@[simp]
/-
**IsSMulRegular.smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：smul_iff (b : S) (ha : IsSMulRegular M a) : IsSMulRegular M (a • b) ↔ IsSM
ulRegular M b
参数：b : S；ha : IsSMulRegular M a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSMulRegular.of_smul`：of_smul (a : R) (ab : IsSMulRegular M (a • s)) : 
IsSMulRegular M s
· 使用定理 `IsSMulRegular.smul`：smul (ra : IsSMulRegular M a) (rs : IsSMulRegular M 
s) : IsSMulRegular M (a • s)

--- 原说明 ---
An element is `M`-regular if and only if multiplying it on the left by an `M`-re
gular element
is `M`-regular.
-/
theorem smul_iff (b : S) (ha : IsSMulRegular M a) : IsSMulRegular M (a • b) ↔ IsSMulRegular M b :=
  ⟨of_smul _, ha.smul⟩
/-
**IsSMulRegular.isLeftRegular** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：isLeftRegular [Mul R] {a : R} (h : IsSMulRegular R a) : IsLeftRegular a
参数：h : IsSMulRegular R a。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isLeftRegular [Mul R] {a : R} (h : IsSMulRegular R a) : IsLeftRegular a :=
  h
/-
**IsSMulRegular.isRightRegular** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：isRightRegular [Mul R] {a : R} (h : IsSMulRegular R (MulOpposite.op a)) : 
IsRightRegular a
参数：h : IsSMulRegular R (MulOpposite.op a)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isRightRegular [Mul R] {a : R} (h : IsSMulRegular R (MulOpposite.op a)) :
    IsRightRegular a :=
  h
/-
**IsSMulRegular.mul** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：mul [Mul R] [IsScalarTower R R M] (ra : IsSMulRegular M a) (rb : IsSMulReg
ular M b) : IsSMulRegular M (a * b)
参数：ra : IsSMulRegular M a；rb : IsSMulRegular M b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSMulRegular.smul`：smul (ra : IsSMulRegular M a) (rs : IsSMulRegular M 
s) : IsSMulRegular M (a • s)
-/
theorem mul [Mul R] [IsScalarTower R R M] (ra : IsSMulRegular M a) (rb : IsSMulRegular M b) :
    IsSMulRegular M (a * b) :=
  ra.smul rb
/-
**IsSMulRegular.of_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：of_mul [Mul R] [IsScalarTower R R M] (ab : IsSMulRegular M (a * b)) : IsSM
ulRegular M b
参数：ab : IsSMulRegular M (a * b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSMulRegular.of_smul`：of_smul (a : R) (ab : IsSMulRegular M (a • s)) : 
IsSMulRegular M s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
-/
theorem of_mul [Mul R] [IsScalarTower R R M] (ab : IsSMulRegular M (a * b)) :
    IsSMulRegular M b := by
  rw [← smul_eq_mul] at ab
  exact ab.of_smul _

@[simp]
/-
**IsSMulRegular.mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：mul_iff_right [Mul R] [IsScalarTower R R M] (ha : IsSMulRegular M a) : IsS
MulRegular M (a * b) ↔ IsSMulRegular M b
参数：ha : IsSMulRegular M a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSMulRegular.of_mul`：of_mul [Mul R] [IsScalarTower R R M] (ab : IsSMulR
egular M (a * b)) : IsSMulRegular M b
· 使用定理 `IsSMulRegular.mul`：mul [Mul R] [IsScalarTower R R M] (ra : IsSMulRegular
 M a) (rb : IsSMulRegular M b) : IsSMulRegular M (a * b)
-/
theorem mul_iff_right [Mul R] [IsScalarTower R R M] (ha : IsSMulRegular M a) :
    IsSMulRegular M (a * b) ↔ IsSMulRegular M b :=
  ⟨of_mul, ha.mul⟩

/-- Two elements `a` and `b` are `M`-regular if and only if both products `a * b` and `b * a`
are `M`-regular. -/
/-
**IsSMulRegular.mul_and_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：mul_and_mul_iff [Mul R] [IsScalarTower R R M] : IsSMulRegular M (a * b) ∧ 
IsSMulRegular M (b * a) ↔ IsSMulRegular M a ∧ IsSMulRegular M b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSMulRegular.of_mul`：of_mul [Mul R] [IsScalarTower R R M] (ab : IsSMulR
egular M (a * b)) : IsSMulRegular M b
· 使用定理 `IsSMulRegular.mul`：mul [Mul R] [IsScalarTower R R M] (ra : IsSMulRegular
 M a) (rb : IsSMulRegular M b) : IsSMulRegular M (a * b)

--- 原说明 ---
Two elements `a` and `b` are `M`-regular if and only if both products `a * b` an
d `b * a`
are `M`-regular.
-/
theorem mul_and_mul_iff [Mul R] [IsScalarTower R R M] :
    IsSMulRegular M (a * b) ∧ IsSMulRegular M (b * a) ↔ IsSMulRegular M a ∧ IsSMulRegular M b := by
  refine ⟨?_, ?_⟩
  · rintro ⟨ab, ba⟩
    exact ⟨ba.of_mul, ab.of_mul⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha.mul hb, hb.mul ha⟩

end SMul

section Monoid

variable [Monoid R] [MulAction R M]
variable (M)

/-- One is always `M`-regular. -/
@[simp]
/-
**IsSMulRegular.one** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：one : IsSMulRegular M (1 : R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
One is always `M`-regular.
-/
theorem one : IsSMulRegular M (1 : R) := fun a b ab => by
  dsimp only [Function.comp_def] at ab
  rw [one_smul, one_smul] at ab
  assumption

variable {M}

/-- An element of `R` admitting a left inverse is `M`-regular. -/
/-
**IsSMulRegular.of_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：of_mul_eq_one (h : a * b = 1) : IsSMulRegular M b
参数：h : a * b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSMulRegular.of_mul`：of_mul [Mul R] [IsScalarTower R R M] (ab : IsSMulR
egular M (a * b)) : IsSMulRegular M b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSMulRegular.one`：one : IsSMulRegular M (1 : R)

--- 原说明 ---
An element of `R` admitting a left inverse is `M`-regular.
-/
theorem of_mul_eq_one (h : a * b = 1) : IsSMulRegular M b :=
  of_mul (a := a) (by rw [h]; exact one M)

/-- Any power of an `M`-regular element is `M`-regular. -/
/-
**IsSMulRegular.pow** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：pow (n : Nat) (ra : IsSMulRegular M a) : IsSMulRegular M (a ^ n)
参数：n : Nat；ra : IsSMulRegular M a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsSMulRegular.smul_iff`：smul_iff (b : S) (ha : IsSMulRegular M a) : IsSM
ulRegular M (a • b) ↔ IsSMulRegular M b

--- 原说明 ---
Any power of an `M`-regular element is `M`-regular.
-/
theorem pow (n : ℕ) (ra : IsSMulRegular M a) : IsSMulRegular M (a ^ n) := by
  induction n with
  | zero => rw [pow_zero]; simp only [one]
  | succ n hn =>
    rw [pow_succ']
    exact (ra.smul_iff (a ^ n)).mpr hn

/-- An element `a` is `M`-regular if and only if a positive power of `a` is `M`-regular. -/
/-
**IsSMulRegular.pow_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：pow_iff {n : Nat} (n0 : 0 < n) : IsSMulRegular M (a ^ n) ↔ IsSMulRegular M
 a
参数：n0 : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `IsSMulRegular.of_smul`：of_smul (a : R) (ab : IsSMulRegular M (a • s)) : 
IsSMulRegular M s
· 使用定理 `IsSMulRegular.pow`：pow (n : Nat) (ra : IsSMulRegular M a) : IsSMulRegula
r M (a ^ n)

--- 原说明 ---
An element `a` is `M`-regular if and only if a positive power of `a` is `M`-regu
lar.
-/
theorem pow_iff {n : ℕ} (n0 : 0 < n) : IsSMulRegular M (a ^ n) ↔ IsSMulRegular M a := by
  refine ⟨?_, pow n⟩
  rw [← Nat.succ_pred_eq_of_pos n0, pow_succ, ← smul_eq_mul]
  exact of_smul _

end Monoid

section MonoidSMul

variable [Monoid S] [SMul R M] [SMul R S] [MulAction S M] [IsScalarTower R S M]

/-- An element of `S` admitting a left inverse in `R` is `M`-regular. -/
/-
**IsSMulRegular.of_smul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：of_smul_eq_one (h : a • s = 1) : IsSMulRegular M s
参数：h : a • s = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSMulRegular.of_smul`：of_smul (a : R) (ab : IsSMulRegular M (a • s)) : 
IsSMulRegular M s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSMulRegular.one`：one : IsSMulRegular M (1 : R)

--- 原说明 ---
An element of `S` admitting a left inverse in `R` is `M`-regular.
-/
theorem of_smul_eq_one (h : a • s = 1) : IsSMulRegular M s :=
  of_smul a
    (by
      rw [h]
      exact one M)

end MonoidSMul

section MonoidWithZero

variable [MonoidWithZero R] [Zero M] [MulActionWithZero R M]

/-- The element `0` is `M`-regular if and only if `M` is trivial. -/
/-
**IsSMulRegular.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : MonoidWithZero R] [inst_1 : Zero M
] [inst_2 : MulActionWithZero R M],   IsSMulRegular M 0 → Subsingleton M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulActionWithZero.zero_smul`：∀ {M₀ : Type u_2} {A : Type u_7} {inst : Mo
noidWithZero M₀} {inst_1 : Zero A} [self : MulActionWithZero M₀ A] (m : A),   0 
• m = 0

--- 原说明 ---
The element `0` is `M`-regular if and only if `M` is trivial.
-/
protected theorem subsingleton (h : IsSMulRegular M (0 : R)) : Subsingleton M :=
  ⟨fun a b => h (by dsimp only [Function.comp_def]; repeat' rw [MulActionWithZero.zero_smul])⟩

/-- The element `0` is `M`-regular if and only if `M` is trivial. -/
/-
**IsSMulRegular.zero_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：zero_iff_subsingleton : IsSMulRegular M (0 : R) ↔ Subsingleton M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSMulRegular.subsingleton`：∀ {R : Type u_1} {M : Type u_3} [inst : Mono
idWithZero R] [inst_1 : Zero M] [inst_2 : MulActionWithZero R M],   IsSMulRegula
r M 0 → Subsingl…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
The element `0` is `M`-regular if and only if `M` is trivial.
-/
theorem zero_iff_subsingleton : IsSMulRegular M (0 : R) ↔ Subsingleton M :=
  ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

/-- The `0` element is not `M`-regular, on a non-trivial module. -/
/-
**IsSMulRegular.not_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：not_zero_iff : ¬IsSMulRegular M (0 : R) ↔ Nontrivial M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nontrivial_iff`：nontrivial_iff : Nontrivial α ↔ exists x y : α, x != y
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `IsSMulRegular.zero_iff_subsingleton`：zero_iff_subsingleton : IsSMulRegul
ar M (0 : R) ↔ Subsingleton M
· 使用定理 `subsingleton_iff`：subsingleton_iff : Subsingleton α ↔ forall x y : α, x 
= y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The `0` element is not `M`-regular, on a non-trivial module.
-/
theorem not_zero_iff : ¬IsSMulRegular M (0 : R) ↔ Nontrivial M := by
  rw [nontrivial_iff, not_iff_comm, zero_iff_subsingleton, subsingleton_iff]
  push Not
  exact Iff.rfl

/-- The element `0` is `M`-regular when `M` is trivial. -/
/-
**IsSMulRegular.zero** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：zero [sM : Subsingleton M] : IsSMulRegular M (0 : R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsSMulRegular.zero_iff_subsingleton`：zero_iff_subsingleton : IsSMulRegul
ar M (0 : R) ↔ Subsingleton M

--- 原说明 ---
The element `0` is `M`-regular when `M` is trivial.
-/
theorem zero [sM : Subsingleton M] : IsSMulRegular M (0 : R) :=
  zero_iff_subsingleton.mpr sM

/-- The `0` element is not `M`-regular, on a non-trivial module. -/
/-
**IsSMulRegular.not_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：not_zero [nM : Nontrivial M] : ¬IsSMulRegular M (0 : R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsSMulRegular.not_zero_iff`：not_zero_iff : ¬IsSMulRegular M (0 : R) ↔ No
ntrivial M

--- 原说明 ---
The `0` element is not `M`-regular, on a non-trivial module.
-/
theorem not_zero [nM : Nontrivial M] : ¬IsSMulRegular M (0 : R) :=
  not_zero_iff.mpr nM

end MonoidWithZero

section CommSemigroup

variable [CommSemigroup R] [SMul R M] [IsScalarTower R R M]

/-- A product is `M`-regular if and only if the factors are. -/
/-
**IsSMulRegular.mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：mul_iff : IsSMulRegular M (a * b) ↔ IsSMulRegular M a ∧ IsSMulRegular M b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSMulRegular.mul_and_mul_iff`：mul_and_mul_iff [Mul R] [IsScalarTower R 
R M] : IsSMulRegular M (a * b) ∧ IsSMulRegular M (b * a) ↔ IsSMulRegular M a ∧ I
sSMulRegular M b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A product is `M`-regular if and only if the factors are.
-/
theorem mul_iff : IsSMulRegular M (a * b) ↔ IsSMulRegular M a ∧ IsSMulRegular M b := by
  rw [← mul_and_mul_iff]
  exact ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩

end CommSemigroup

end IsSMulRegular

section Group

variable {G : Type*} [Group G]

/-- An element of a group acting on a Type is regular. This relies on the availability
of the inverse given by groups, since there is no `LeftCancelSMul` typeclass. -/
/-
**isSMulRegular_of_group** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSMulRegular_of_group [MulAction G R] (g : G) : IsSMulRegular R g
参数：g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
An element of a group acting on a Type is regular. This relies on the availabili
ty
of the inverse given by groups, since there is no `LeftCancelSMul` typeclass.
-/
theorem isSMulRegular_of_group [MulAction G R] (g : G) : IsSMulRegular R g := by
  intro x y h
  convert congr_arg (g⁻¹ • ·) h <;> simp [← smul_assoc]

end Group

section Units

variable (M) [Monoid R] [MulAction R M]

/-- Any element in `Rˣ` is `M`-regular. -/
/-
**Units.isSMulRegular** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.isSMulRegular (a : Rˣ) : IsSMulRegular M (a : R)
参数：a : Rˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSMulRegular.of_mul_eq_one`：of_mul_eq_one (h : a * b = 1) : IsSMulRegul
ar M b
· 使用定理 `Units.inv_val`：∀ {α : Type u} [inst : Monoid α] (self : αˣ), self.inv * 
↑self = 1

--- 原说明 ---
Any element in `Rˣ` is `M`-regular.
-/
theorem Units.isSMulRegular (a : Rˣ) : IsSMulRegular M (a : R) :=
  IsSMulRegular.of_mul_eq_one a.inv_val

/-- A unit is `M`-regular. -/
/-
**IsUnit.isSMulRegular** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUnit.isSMulRegular (ua : IsUnit a) : IsSMulRegular M a
参数：ua : IsUnit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isSMulRegular`：Units.isSMulRegular (a : Rˣ) : IsSMulRegular M (a :
 R)

--- 原说明 ---
A unit is `M`-regular.
-/
theorem IsUnit.isSMulRegular (ua : IsUnit a) : IsSMulRegular M a := by
  rcases ua with ⟨a, rfl⟩
  exact a.isSMulRegular M

end Units

section SMulZeroClass

/-
**IsSMulRegular.right_eq_zero_of_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsSMulRegular`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : Zero M] [inst_1 : SMulZeroClass R 
M] {r : R} {x : M},   IsSMulRegular M r → r • x = 0 → x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
protected lemma IsSMulRegular.right_eq_zero_of_smul [Zero M] [SMulZeroClass R M]
    {r : R} {x : M} (h1 : IsSMulRegular M r) (h2 : r • x = 0) : x = 0 :=
  h1 (h2.trans (smul_zero r).symm)

end SMulZeroClass

/-
**isSMulRegular_iff_right_eq_zero_of_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSMulRegular_iff_right_eq_zero_of_smul [AddGroup M] [DistribSMul R M] {r 
: R} : IsSMulRegular M r ↔ forall m : M, r • m = 0 -> m = 0 where mp h _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSMulRegular.right_eq_zero_of_smul`：∀ {R : Type u_1} {M : Type u_3} [in
st : Zero M] [inst_1 : SMulZeroClass R M] {r : R} {x : M},   IsSMulRegular M r →
 r • x = 0 → x = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isSMulRegular_iff_right_eq_zero_of_smul [AddGroup M] [DistribSMul R M] {r : R} :
    IsSMulRegular M r ↔ ∀ m : M, r • m = 0 → m = 0 where
  mp h _ := h.right_eq_zero_of_smul
  mpr h m₁ m₂ eq := sub_eq_zero.mp <| h _ <| by simp_rw [smul_sub, eq, sub_self]

alias ⟨_, IsSMulRegular.of_right_eq_zero_of_smul⟩ := isSMulRegular_iff_right_eq_zero_of_smul
/-
**Equiv.isSMulRegular_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Equiv.isSMulRegular_congr {R S M M'} [SMul R M] [SMul S M'] {e : M ≃ M'} {
r : R} {s : S} (h : forall x, e (r • x) = s • e x) : IsSMulRegular M r ↔ IsSMulR
egular M' s
参数：h : forall x, e (r • x) = s • e x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.comp_injective`：comp_injective (f : α -> β) (e : β ≃ γ) : Injectiv
e (e ∘ f) ↔ Injective f
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.injective_comp`：injective_comp (e : α ≃ β) (f : β -> γ) : Injectiv
e (f ∘ e) ↔ Injective f
-/
lemma Equiv.isSMulRegular_congr {R S M M'} [SMul R M] [SMul S M'] {e : M ≃ M'}
    {r : R} {s : S} (h : ∀ x, e (r • x) = s • e x) :
    IsSMulRegular M r ↔ IsSMulRegular M' s :=
  (e.comp_injective _).symm.trans <|
    (iff_of_eq <| congrArg _ <| funext h).trans <| e.injective_comp _
