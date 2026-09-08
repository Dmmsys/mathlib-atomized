/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.Order.CauSeq.Basic
public import Mathlib.Algebra.Ring.Action.Rat
public import Mathlib.Tactic.FastInstance

/-!
# Cauchy completion

This file generalizes the Cauchy completion of `(ℚ, abs)` to the completion of a ring
with absolute value.
-/

@[expose] public section


namespace CauSeq.Completion

open CauSeq

section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

-- TODO: rename this to `CauSeq.Completion` instead of `CauSeq.Completion.Cauchy`.
/-- The Cauchy completion of a ring with absolute value. -/
/-
**CauSeq.Completion.Cauchy** 是 Mathlib 中的一个定义，位于命名空间 `CauSeq.Completion`。
形式化陈述：Cauchy
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cauchy completion of a ring with absolute value.
-/
def Cauchy :=
  @Quotient (CauSeq _ abv) CauSeq.equiv

variable {abv}

/-- The map from Cauchy sequences into the Cauchy completion. -/
/-
**CauSeq.Completion.mk** 是 Mathlib 中的一个定义，位于命名空间 `CauSeq.Completion`。
形式化陈述：mk : CauSeq _ abv -> Cauchy abv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
The map from Cauchy sequences into the Cauchy completion.
-/
def mk : CauSeq _ abv → Cauchy abv :=
  Quotient.mk''

@[simp]
/-
**CauSeq.Completion.mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：mk_eq_mk (f : CauSeq _ abv) : @Eq (Cauchy abv) ⟦f⟧ (mk f)
参数：f : CauSeq _ abv。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_eq_mk (f : CauSeq _ abv) : @Eq (Cauchy abv) ⟦f⟧ (mk f) :=
  rfl
/-
**CauSeq.Completion.mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：mk_eq {f g : CauSeq _ abv} : mk f = mk g ↔ LimZero (f - g)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
theorem mk_eq {f g : CauSeq _ abv} : mk f = mk g ↔ LimZero (f - g) :=
  Quotient.eq

/-- The map from the original ring into the Cauchy completion. -/
/-
**CauSeq.Completion.ofRat** 是 Mathlib 中的一个定义，位于命名空间 `CauSeq.Completion`。
形式化陈述：ofRat (x : β) : Cauchy abv
参数：x : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the original ring into the Cauchy completion.
-/
def ofRat (x : β) : Cauchy abv :=
  mk (const abv x)
/-
**CauSeq.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (Cauchy abv) :=
  ⟨ofRat 0⟩
/-
**CauSeq.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (Cauchy abv) :=
  ⟨ofRat 1⟩
/-
**CauSeq.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Cauchy abv) :=
  ⟨0⟩
/-
**CauSeq.Completion.ofRat_zero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：ofRat_zero : (ofRat 0 : Cauchy abv) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofRat_zero : (ofRat 0 : Cauchy abv) = 0 :=
  rfl
/-
**CauSeq.Completion.ofRat_one** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：ofRat_one : (ofRat 1 : Cauchy abv) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofRat_one : (ofRat 1 : Cauchy abv) = 1 :=
  rfl

@[simp]
/-
**CauSeq.Completion.mk_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：mk_eq_zero {f : CauSeq _ abv} : mk f = 0 ↔ LimZero f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem mk_eq_zero {f : CauSeq _ abv} : mk f = 0 ↔ LimZero f := by
  have : mk f = 0 ↔ LimZero (f - 0) := Quotient.eq
  rwa [sub_zero] at this
/-
**CauSeq.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (Cauchy abv) :=
  ⟨(Quotient.map₂ (· + ·)) fun _ _ hf _ _ hg => add_equiv_add hf hg⟩

@[simp]
/-
**CauSeq.Completion.mk_add** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：mk_add (f g : CauSeq β abv) : mk f + mk g = mk (f + g)
参数：f g : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_add (f g : CauSeq β abv) : mk f + mk g = mk (f + g) :=
  rfl
/-
**CauSeq.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (Cauchy abv) :=
  ⟨(Quotient.map Neg.neg) fun _ _ hf => neg_equiv_neg hf⟩

@[simp]
/-
**CauSeq.Completion.mk_neg** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：mk_neg (f : CauSeq β abv) : -mk f = mk (-f)
参数：f : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_neg (f : CauSeq β abv) : -mk f = mk (-f) :=
  rfl
/-
**CauSeq.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (Cauchy abv) :=
  ⟨(Quotient.map₂ (· * ·)) fun _ _ hf _ _ hg => mul_equiv_mul hf hg⟩

@[simp]
/-
**CauSeq.Completion.mk_mul** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：mk_mul (f g : CauSeq β abv) : mk f * mk g = mk (f * g)
参数：f g : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_mul (f g : CauSeq β abv) : mk f * mk g = mk (f * g) :=
  rfl
/-
**CauSeq.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (Cauchy abv) :=
  ⟨(Quotient.map₂ Sub.sub) fun _ _ hf _ _ hg => sub_equiv_sub hf hg⟩

@[simp]
/-
**CauSeq.Completion.mk_sub** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：mk_sub (f g : CauSeq β abv) : mk f - mk g = mk (f - g)
参数：f g : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_sub (f g : CauSeq β abv) : mk f - mk g = mk (f - g) :=
  rfl
/-
**CauSeq.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {γ : Type*} [SMul γ β] [IsScalarTower γ β β] : SMul γ (Cauchy abv) :=
  ⟨fun c => (Quotient.map (c • ·)) fun _ _ hf => smul_equiv_smul _ hf⟩

@[simp]
/-
**CauSeq.Completion.mk_smul** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：mk_smul {γ : Type*} [SMul γ β] [IsScalarTower γ β β] (c : γ) (f : CauSeq β
 abv) : c • mk f = mk (c • f)
参数：c : γ；f : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_smul {γ : Type*} [SMul γ β] [IsScalarTower γ β β] (c : γ) (f : CauSeq β abv) :
    c • mk f = mk (c • f) :=
  rfl
/-
**CauSeq.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (Cauchy abv) ℕ :=
  ⟨fun x n => Quotient.map (· ^ n) (fun _ _ hf => pow_equiv_pow hf _) x⟩

@[simp]
/-
**CauSeq.Completion.mk_pow** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：mk_pow (n : Nat) (f : CauSeq β abv) : mk f ^ n = mk (f ^ n)
参数：n : Nat；f : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_pow (n : ℕ) (f : CauSeq β abv) : mk f ^ n = mk (f ^ n) :=
  rfl
/-
**CauSeq.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast (Cauchy abv) :=
  ⟨fun n => mk n⟩
/-
**CauSeq.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IntCast (Cauchy abv) :=
  ⟨fun n => mk n⟩

@[simp]
/-
**CauSeq.Completion.ofRat_natCast** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：ofRat_natCast (n : Nat) : (ofRat n : Cauchy abv) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofRat_natCast (n : ℕ) : (ofRat n : Cauchy abv) = n :=
  rfl

@[simp]
/-
**CauSeq.Completion.ofRat_intCast** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：ofRat_intCast (z : Int) : (ofRat z : Cauchy abv) = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofRat_intCast (z : ℤ) : (ofRat z : Cauchy abv) = z :=
  rfl
/-
**CauSeq.Completion.ofRat_add** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：ofRat_add (x y : β) : ofRat (x + y) = (ofRat x + ofRat y : Cauchy abv)
参数：x y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CauSeq.const_add`：const_add (x y : β) : const (x + y) = const x + const 
y
-/
theorem ofRat_add (x y : β) :
    ofRat (x + y) = (ofRat x + ofRat y : Cauchy abv) :=
  congr_arg mk (const_add _ _)
/-
**CauSeq.Completion.ofRat_neg** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：ofRat_neg (x : β) : ofRat (-x) = (-ofRat x : Cauchy abv)
参数：x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CauSeq.const_neg`：const_neg (x : β) : const (-x) = -const x
-/
theorem ofRat_neg (x : β) : ofRat (-x) = (-ofRat x : Cauchy abv) :=
  congr_arg mk (const_neg _)
/-
**CauSeq.Completion.ofRat_mul** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：ofRat_mul (x y : β) : ofRat (x * y) = (ofRat x * ofRat y : Cauchy abv)
参数：x y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CauSeq.const_mul`：const_mul (x y : β) : const (x * y) = const x * const 
y
-/
theorem ofRat_mul (x y : β) :
    ofRat (x * y) = (ofRat x * ofRat y : Cauchy abv) :=
  congr_arg mk (const_mul _ _)
/-
**CauSeq.Completion.ofRat_injective** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion
`。
形式化陈述：ofRat_injective : Function.Injective (ofRat : β -> Cauchy abv)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem ofRat_injective : Function.Injective (ofRat : β → Cauchy abv) := fun x y h => by
  simpa [ofRat, mk_eq, ← const_sub, const_limZero, sub_eq_zero] using h
/-
**CauSeq.Completion.Cauchy.ring** 是 Mathlib 中的一个定义，位于命名空间 `CauSeq.Completion.Cau
chy`。
形式化陈述：{α : Type u_1} →   [inst : Field α] →     [inst_1 : LinearOrder α] →      
 [inst_2 : IsStrictOrderedRing α] →         {β : Type u_2} →           [inst_3 :
 Ring β] → {abv : β → α} → [inst_4 : IsAbsoluteValue abv] → Ring (CauSeq.Complet
ion.Cauchy abv)
参数：CauSeq.Completion.Cauchy abv。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Cauchy.ring : Ring (Cauchy abv) := fast_instance%
  Function.Surjective.ring mk Quotient.mk'_surjective rfl rfl
    (fun _ _ => (mk_add _ _).symm) (fun _ _ => (mk_mul _ _).symm) (fun _ => (mk_neg _).symm)
    (fun _ _ => (mk_sub _ _).symm) (fun _ _ => (mk_smul _ _).symm) (fun _ _ => (mk_smul _ _).symm)
    (fun _ _ => (mk_pow _ _).symm) (fun _ => rfl) fun _ => rfl

/-- `CauSeq.Completion.ofRat` as a `RingHom` -/
@[simps]
/-
**CauSeq.Completion.ofRatRingHom** 是 Mathlib 中的一个定义，位于命名空间 `CauSeq.Completion`。
形式化陈述：ofRatRingHom : β ->+* (Cauchy abv) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.Completion.ofRat_one`：ofRat_one : (ofRat 1 : Cauchy abv) = 1
· 使用定理 `CauSeq.Completion.ofRat_mul`：ofRat_mul (x y : β) : ofRat (x * y) = (ofRa
t x * ofRat y : Cauchy abv)
· 使用定理 `CauSeq.Completion.ofRat_zero`：ofRat_zero : (ofRat 0 : Cauchy abv) = 0
· 使用定理 `CauSeq.Completion.ofRat_add`：ofRat_add (x y : β) : ofRat (x + y) = (ofRa
t x + ofRat y : Cauchy abv)

--- 原说明 ---
`CauSeq.Completion.ofRat` as a `RingHom`
-/
def ofRatRingHom : β →+* (Cauchy abv) where
  toFun := ofRat
  map_zero' := ofRat_zero
  map_one' := ofRat_one
  map_add' := ofRat_add
  map_mul' := ofRat_mul
/-
**CauSeq.Completion.ofRat_sub** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：ofRat_sub (x y : β) : ofRat (x - y) = (ofRat x - ofRat y : Cauchy abv)
参数：x y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CauSeq.const_sub`：const_sub (x y : β) : const (x - y) = const x - const 
y
-/
theorem ofRat_sub (x y : β) : ofRat (x - y) = (ofRat x - ofRat y : Cauchy abv) :=
  congr_arg mk (const_sub _ _)
/-
**CauSeq.Completion.Cauchy.instNonTrivial** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Comp
letion.Cauchy`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {β : Type u_2}   [inst_3 : Ring β] {abv : β → α} [inst_4 : IsA
bsoluteValue abv] [Nontrivial β],   Nontrivial (CauSeq.Completion.Cauchy abv)
参数：CauSeq.Completion.Cauchy abv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `CauSeq.Completion.ofRat_injective`：ofRat_injective : Function.Injective 
(ofRat : β -> Cauchy abv)
-/
noncomputable instance Cauchy.instNonTrivial [Nontrivial β] : Nontrivial (Cauchy abv) :=
  ofRat_injective.nontrivial

end

section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type*} [CommRing β] {abv : β → α} [IsAbsoluteValue abv]

/-
**CauSeq.Completion.Cauchy.commRing** 是 Mathlib 中的一个定义，位于命名空间 `CauSeq.Completion
.Cauchy`。
形式化陈述：{α : Type u_1} →   [inst : Field α] →     [inst_1 : LinearOrder α] →      
 [inst_2 : IsStrictOrderedRing α] →         {β : Type u_2} →           [inst_3 :
 CommRing β] →             {abv : β → α} → [inst_4 : IsAbsoluteValue abv] → Comm
Ring (CauSeq.Completion.Cauchy abv)
参数：CauSeq.Completion.Cauchy abv。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Cauchy.commRing : CommRing (Cauchy abv) := fast_instance%
  Function.Surjective.commRing mk Quotient.mk'_surjective rfl rfl
    (fun _ _ => (mk_add _ _).symm) (fun _ _ => (mk_mul _ _).symm) (fun _ => (mk_neg _).symm)
    (fun _ _ => (mk_sub _ _).symm) (fun _ _ => (mk_smul _ _).symm) (fun _ _ => (mk_smul _ _).symm)
    (fun _ _ => (mk_pow _ _).symm) (fun _ => rfl) fun _ => rfl

end

section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type*} [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

/-
**CauSeq.Completion.instNNRatCast** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq.Completion`。
形式化陈述：instNNRatCast : NNRatCast (Cauchy abv) where nnratCast q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNNRatCast : NNRatCast (Cauchy abv) where nnratCast q := ofRat q
/-
**CauSeq.Completion.instRatCast** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq.Completion`。
形式化陈述：instRatCast : RatCast (Cauchy abv) where ratCast q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRatCast : RatCast (Cauchy abv) where ratCast q := ofRat q
/-
**CauSeq.Completion.ofRat_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion
`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {β : Type u_2}   [inst_3 : DivisionRing β] {abv : β → α} [inst
_4 : IsAbsoluteValue abv] (q : ℚ≥0), CauSeq.Completion.ofRat ↑q = ↑q
参数：q : ℚ≥0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ofRat_nnratCast (q : ℚ≥0) : ofRat (q : β) = (q : Cauchy abv) := rfl
/-
**CauSeq.Completion.ofRat_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {β : Type u_2}   [inst_3 : DivisionRing β] {abv : β → α} [inst
_4 : IsAbsoluteValue abv] (q : ℚ), CauSeq.Completion.ofRat ↑q = ↑q
参数：q : ℚ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ofRat_ratCast (q : ℚ) : ofRat (q : β) = (q : Cauchy abv) := rfl

open scoped Classical in
/-
**CauSeq.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Inv (Cauchy abv) :=
  ⟨fun x =>
    (Quotient.liftOn x fun f => mk <| if h : LimZero f then 0 else inv f h) fun f g fg => by
      have := limZero_congr fg
      by_cases hf : LimZero f
      · simp [hf, this.1 hf]
      · have hg := mt this.2 hf
        simp only [hf, dite_false, hg]
        have If : mk (inv f hf) * mk f = 1 := mk_eq.2 (inv_mul_cancel hf)
        have Ig : mk (inv g hg) * mk g = 1 := mk_eq.2 (inv_mul_cancel hg)
        have Ig' : mk g * mk (inv g hg) = 1 := mk_eq.2 (mul_inv_cancel hg)
        rw [mk_eq.2 fg, ← Ig] at If
        rw [← mul_one (mk (inv f hf)), ← Ig', ← mul_assoc, If, mul_assoc, Ig', mul_one]⟩
/-
**CauSeq.Completion.inv_zero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：inv_zero : (0 : (Cauchy abv))⁻¹ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CauSeq.zero_limZero`：∀ {α : Type u_1} {β : Type u_2} [inst : Field α] [i
nst_1 : LinearOrder α] [inst_2 : IsStrictOrderedRing α]   [inst_3 : Ring β] {abv
 : β → α}…
-/
theorem inv_zero : (0 : (Cauchy abv))⁻¹ = 0 :=
  congr_arg mk <| by rw [dif_pos] <;> [rfl; exact zero_limZero]

@[simp]
/-
**CauSeq.Completion.inv_mk** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：inv_mk {f} (hf) : (mk (abv
参数：hf。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem inv_mk {f} (hf) : (mk (abv := abv) f)⁻¹ = mk (inv f hf) :=
  congr_arg mk <| by rw [dif_neg]
/-
**CauSeq.Completion.cau_seq_zero_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Comple
tion`。
形式化陈述：cau_seq_zero_ne_one : ¬(0 : CauSeq _ abv) ≈ 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CauSeq.const_limZero`：const_limZero {x : β} : LimZero (const x) ↔ x = 0
-/
theorem cau_seq_zero_ne_one : ¬(0 : CauSeq _ abv) ≈ 1 := fun h ↦
  have : LimZero (1 - 0 : CauSeq _ abv) := Setoid.symm h
  have : LimZero (1 : CauSeq _ abv) := by simpa
  one_ne_zero <| const_limZero.1 this
/-
**CauSeq.Completion.zero_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：zero_ne_one : (0 : (Cauchy abv)) != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.Completion.cau_seq_zero_ne_one`：cau_seq_zero_ne_one : ¬(0 : CauSe
q _ abv) ≈ 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CauSeq.Completion.mk_eq`：mk_eq {f g : CauSeq _ abv} : mk f = mk g ↔ LimZ
ero (f - g)
-/
theorem zero_ne_one : (0 : (Cauchy abv)) ≠ 1 := fun h => cau_seq_zero_ne_one <| mk_eq.1 h
/-
**CauSeq.Completion.inv_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`
。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {β : Type u_2}   [inst_3 : DivisionRing β] {abv : β → α} [inst
_4 : IsAbsoluteValue abv] {x : CauSeq.Completion.Cauchy abv},   x ≠ 0 → x⁻¹ * x 
= 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CauSeq.Completion.inv_mk`：inv_mk {f} (hf) : (mk (abv
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `CauSeq.inv_mul_cancel`：inv_mul_cancel {f : CauSeq β abv} (hf) : inv f hf
 * f ≈ 1
-/
protected theorem inv_mul_cancel {x : (Cauchy abv)} : x ≠ 0 → x⁻¹ * x = 1 :=
  Quotient.inductionOn x fun f hf => by
    simp only [mk_eq_mk, ne_eq, mk_eq_zero] at hf
    simp only [mk_eq_mk, hf, not_false_eq_true, inv_mk, mk_mul]
    exact Quotient.sound (CauSeq.inv_mul_cancel hf)
/-
**CauSeq.Completion.mul_inv_cancel** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`
。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {β : Type u_2}   [inst_3 : DivisionRing β] {abv : β → α} [inst
_4 : IsAbsoluteValue abv] {x : CauSeq.Completion.Cauchy abv},   x ≠ 0 → x * x⁻¹ 
= 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CauSeq.Completion.inv_mk`：inv_mk {f} (hf) : (mk (abv
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `CauSeq.mul_inv_cancel`：mul_inv_cancel {f : CauSeq β abv} (hf) : f * inv 
f hf ≈ 1
-/
protected theorem mul_inv_cancel {x : (Cauchy abv)} : x ≠ 0 → x * x⁻¹ = 1 :=
  Quotient.inductionOn x fun f hf => by
    simp only [mk_eq_mk, ne_eq, mk_eq_zero] at hf
    simp only [mk_eq_mk, hf, not_false_eq_true, inv_mk, mk_mul]
    exact Quotient.sound (CauSeq.mul_inv_cancel hf)
/-
**CauSeq.Completion.ofRat_inv** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq.Completion`。
形式化陈述：ofRat_inv (x : β) : ofRat x⁻¹ = ((ofRat x)⁻¹ : (Cauchy abv))
参数：x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CauSeq.const.congr_simp`：∀ {α : Type u_1} {β : Type u_2} [inst : Field α
] [inst_1 : LinearOrder α] [inst_2 : IsStrictOrderedRing α]   [inst_3 : Ring β] 
(abv : β → α)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CauSeq.const_limZero`：const_limZero {x : β} : LimZero (const x) ↔ x = 0
· 使用定理 `GroupWithZero.inv_zero`：∀ {G₀ : Type u} [self : GroupWithZero G₀], 0⁻¹ =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem ofRat_inv (x : β) : ofRat x⁻¹ = ((ofRat x)⁻¹ : (Cauchy abv)) :=
  congr_arg mk <| by split_ifs with h <;>
    [simp only [const_limZero.1 h, GroupWithZero.inv_zero, const_zero]; rfl]
/-
**CauSeq.Completion.instDivInvMonoid** 是 Mathlib 中的一个定义，位于命名空间 `CauSeq.Completio
n`。
形式化陈述：{α : Type u_1} →   [inst : Field α] →     [inst_1 : LinearOrder α] →      
 [inst_2 : IsStrictOrderedRing α] →         {β : Type u_2} →           [inst_3 :
 DivisionRing β] →             {abv : β → α} → [inst_4 : IsAbsoluteValue abv] → 
DivInvMonoid (CauSeq.Completion.Cauchy abv)
参数：CauSeq.Completion.Cauchy abv。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instDivInvMonoid : DivInvMonoid (Cauchy abv) where
/-
**CauSeq.Completion.ofRat_div** 是 Mathlib 中的一个引理，位于命名空间 `CauSeq.Completion`。
形式化陈述：ofRat_div (x y : β) : ofRat (x / y) = (ofRat x / ofRat y : Cauchy abv)
参数：x y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `CauSeq.Completion.ofRat_mul`：ofRat_mul (x y : β) : ofRat (x * y) = (ofRa
t x * ofRat y : Cauchy abv)
· 使用定理 `CauSeq.Completion.ofRat_inv`：ofRat_inv (x : β) : ofRat x⁻¹ = ((ofRat x)⁻
¹ : (Cauchy abv))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofRat_div (x y : β) : ofRat (x / y) = (ofRat x / ofRat y : Cauchy abv) := by
  simp only [div_eq_mul_inv, ofRat_inv, ofRat_mul]

/-- The Cauchy completion forms a division ring. -/
/-
**CauSeq.Completion.Cauchy.divisionRing** 是 Mathlib 中的一个定义，位于命名空间 `CauSeq.Comple
tion.Cauchy`。
形式化陈述：{α : Type u_1} →   [inst : Field α] →     [inst_1 : LinearOrder α] →      
 [inst_2 : IsStrictOrderedRing α] →         {β : Type u_2} →           [inst_3 :
 DivisionRing β] →             {abv : β → α} → [inst_4 : IsAbsoluteValue abv] → 
DivisionRing (CauSeq.Completion.Cauchy abv)
参数：CauSeq.Completion.Cauchy abv。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.Completion.mul_inv_cancel`：∀ {α : Type u_1} [inst : Field α] [ins
t_1 : LinearOrder α] [inst_2 : IsStrictOrderedRing α] {β : Type u_2}   [inst_3 :
 DivisionRing β] {abv …
· 使用定理 `CauSeq.Completion.inv_zero`：inv_zero : (0 : (Cauchy abv))⁻¹ = 0

--- 原说明 ---
The Cauchy completion forms a division ring.
-/
noncomputable instance Cauchy.divisionRing : DivisionRing (Cauchy abv) where
  inv_zero := inv_zero
  mul_inv_cancel _ := CauSeq.Completion.mul_inv_cancel
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by simp_rw [← ofRat_nnratCast, NNRat.cast_def, ofRat_div, ofRat_natCast]
  ratCast_def q := by rw [← ofRat_ratCast, Rat.cast_def, ofRat_div, ofRat_natCast, ofRat_intCast]
  nnqsmul_def _ x := Quotient.inductionOn x fun _ ↦ congr_arg mk <| ext fun _ ↦ NNRat.smul_def _ _
  qsmul_def _ x := Quotient.inductionOn x fun _ ↦ congr_arg mk <| ext fun _ ↦ Rat.smul_def _ _

/-- Show the first 10 items of a representative of this equivalence class of Cauchy sequences.

The representative chosen is the one passed in the VM to `Quot.mk`, so two Cauchy sequences
converging to the same number may be printed differently.
-/
/-
**CauSeq.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show the first 10 items of a representative of this equivalence class of Cauchy 
sequences.

The representative chosen is the one passed in the VM to `Quot.mk`, so two Cauch
y sequences
converging to the same number may be printed differently.
-/
unsafe instance [Repr β] : Repr (Cauchy abv) where
  reprPrec r _ :=
    let N := 10
    let seq := r.unquot
    "(sorry /- " ++ Std.Format.joinSep ((List.range N).map <| repr ∘ seq) ", " ++ ", ... -/)"

end

section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type*} [Field β] {abv : β → α} [IsAbsoluteValue abv]

/-- The Cauchy completion forms a field. -/
/-
**CauSeq.Completion.Cauchy.field** 是 Mathlib 中的一个定义，位于命名空间 `CauSeq.Completion.Ca
uchy`。
形式化陈述：{α : Type u_1} →   [inst : Field α] →     [inst_1 : LinearOrder α] →      
 [inst_2 : IsStrictOrderedRing α] →         {β : Type u_2} →           [inst_3 :
 Field β] → {abv : β → α} → [inst_4 : IsAbsoluteValue abv] → Field (CauSeq.Compl
etion.Cauchy abv)
参数：CauSeq.Completion.Cauchy abv。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cauchy completion forms a field.
-/
noncomputable instance Cauchy.field : Field (Cauchy abv) :=
  { Cauchy.divisionRing, Cauchy.commRing with }

end

end CauSeq.Completion

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

namespace CauSeq

section

variable (β : Type*) [Ring β] (abv : β → α) [IsAbsoluteValue abv]

/-- A class stating that a ring with an absolute value is complete, i.e. every Cauchy
sequence has a limit. -/
/-
**CauSeq.IsComplete** 是 Mathlib 中的一个归纳类型，位于命名空间 `CauSeq`。
形式化陈述：{α : Type u_1} →   [inst : Field α] →     [inst_1 : LinearOrder α] →      
 [IsStrictOrderedRing α] → (β : Type u_2) → [inst_3 : Ring β] → (abv : β → α) → 
[IsAbsoluteValue abv] → Prop
参数：β : Type u_2；abv : β → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class stating that a ring with an absolute value is complete, i.e. every Cauch
y
sequence has a limit.
-/
class IsComplete : Prop where
  /-- Every Cauchy sequence has a limit. -/
  isComplete : ∀ s : CauSeq β abv, ∃ b : β, s ≈ const abv b

end

section

variable {β : Type*} [Ring β] {abv : β → α} [IsAbsoluteValue abv]
variable [IsComplete β abv]

/-
**CauSeq.complete** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：complete : forall s : CauSeq β abv, exists b : β, s ≈ const abv b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.IsComplete.isComplete`：∀ {α : Type u_1} {inst : Field α} {inst_1 
: LinearOrder α} {inst_2 : IsStrictOrderedRing α} {β : Type u_2}   {inst_3 : Rin
g β} {abv : β → α}…
-/
theorem complete : ∀ s : CauSeq β abv, ∃ b : β, s ≈ const abv b :=
  IsComplete.isComplete

/-- The limit of a Cauchy sequence in a complete ring. Chosen non-computably. -/
/-
**CauSeq.lim** 是 Mathlib 中的一个定义，位于命名空间 `CauSeq`。
形式化陈述：lim (s : CauSeq β abv) : β
参数：s : CauSeq β abv。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.complete`：complete : forall s : CauSeq β abv, exists b : β, s ≈ c
onst abv b

--- 原说明 ---
The limit of a Cauchy sequence in a complete ring. Chosen non-computably.
-/
noncomputable def lim (s : CauSeq β abv) : β :=
  Classical.choose (complete s)
/-
**CauSeq.equiv_lim** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s)
参数：s : CauSeq β abv。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `CauSeq.complete`：complete : forall s : CauSeq β abv, exists b : β, s ≈ c
onst abv b
-/
theorem equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s) :=
  Classical.choose_spec (complete s)
/-
**CauSeq.eq_lim_of_const_equiv** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：eq_lim_of_const_equiv {f : CauSeq β abv} {x : β} (h : CauSeq.const abv x ≈
 f) : x = lim f
参数：h : CauSeq.const abv x ≈ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CauSeq.const_equiv`：const_equiv {x y : β} : const x ≈ const y ↔ x = y
· 使用定理 `Setoid.trans`：∀ {α : Sort u} [inst : Setoid α] {a b c : α}, a ≈ b → b ≈ 
c → a ≈ c
· 使用定理 `CauSeq.equiv_lim`：equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s)
-/
theorem eq_lim_of_const_equiv {f : CauSeq β abv} {x : β} (h : CauSeq.const abv x ≈ f) : x = lim f :=
  const_equiv.mp <| Setoid.trans h <| equiv_lim f
/-
**CauSeq.lim_eq_of_equiv_const** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：lim_eq_of_equiv_const {f : CauSeq β abv} {x : β} (h : f ≈ CauSeq.const abv
 x) : lim f = x
参数：h : f ≈ CauSeq.const abv x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CauSeq.eq_lim_of_const_equiv`：eq_lim_of_const_equiv {f : CauSeq β abv} {
x : β} (h : CauSeq.const abv x ≈ f) : x = lim f
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
-/
theorem lim_eq_of_equiv_const {f : CauSeq β abv} {x : β} (h : f ≈ CauSeq.const abv x) : lim f = x :=
  (eq_lim_of_const_equiv <| Setoid.symm h).symm
/-
**CauSeq.lim_eq_lim_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：lim_eq_lim_of_equiv {f g : CauSeq β abv} (h : f ≈ g) : lim f = lim g
参数：h : f ≈ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.lim_eq_of_equiv_const`：lim_eq_of_equiv_const {f : CauSeq β abv} {
x : β} (h : f ≈ CauSeq.const abv x) : lim f = x
· 使用定理 `Setoid.trans`：∀ {α : Sort u} [inst : Setoid α] {a b c : α}, a ≈ b → b ≈ 
c → a ≈ c
· 使用定理 `CauSeq.equiv_lim`：equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s)
-/
theorem lim_eq_lim_of_equiv {f g : CauSeq β abv} (h : f ≈ g) : lim f = lim g :=
  lim_eq_of_equiv_const <| Setoid.trans h <| equiv_lim g

@[simp]
/-
**CauSeq.lim_const** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：lim_const (x : β) : lim (const abv x) = x
参数：x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.lim_eq_of_equiv_const`：lim_eq_of_equiv_const {f : CauSeq β abv} {
x : β} (h : f ≈ CauSeq.const abv x) : lim f = x
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
-/
theorem lim_const (x : β) : lim (const abv x) = x :=
  lim_eq_of_equiv_const <| Setoid.refl _
/-
**CauSeq.lim_add** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：lim_add (f g : CauSeq β abv) : lim f + lim g = lim (f + g)
参数：f g : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.eq_lim_of_const_equiv`：eq_lim_of_const_equiv {f : CauSeq β abv} {
x : β} (h : CauSeq.const abv x ≈ f) : x = lim f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CauSeq.const_add`：const_add (x y : β) : const (x + y) = const x + const 
y
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `CauSeq.add_limZero`：add_limZero {f g : CauSeq β abv} (hf : LimZero f) (h
g : LimZero g) : LimZero (f + g) | ε, ε0 => (exists_forall_ge_and (hf _ <| half_
pos ε0) …
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `CauSeq.equiv_lim`：equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s)
-/
theorem lim_add (f g : CauSeq β abv) : lim f + lim g = lim (f + g) :=
  eq_lim_of_const_equiv <|
    show LimZero (const abv (lim f + lim g) - (f + g)) by
      rw [const_add, add_sub_add_comm]
      exact add_limZero (Setoid.symm (equiv_lim f)) (Setoid.symm (equiv_lim g))
/-
**CauSeq.lim_mul_lim** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：lim_mul_lim (f g : CauSeq β abv) : lim f * lim g = lim (f * g)
参数：f g : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.eq_lim_of_const_equiv`：eq_lim_of_const_equiv {f : CauSeq β abv} {
x : β} (h : CauSeq.const abv x ≈ f) : x = lim f
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CauSeq.coe_add`：coe_add (f g : CauSeq β abv) : ⇑(f + g) = (f : Nat -> β)
 + g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `sub_add_sub_cancel'`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G
), a - b + (c - a) = c - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CauSeq.add_limZero`：add_limZero {f g : CauSeq β abv} (hf : LimZero f) (h
g : LimZero g) : LimZero (f + g) | ε, ε0 => (exists_forall_ge_and (hf _ <| half_
pos ε0) …
· 使用定理 `CauSeq.mul_limZero_left`：mul_limZero_left {f} (g : CauSeq β abv) (hg : L
imZero f) : LimZero (f * g) | ε, ε0 => let ⟨G, G0, hG⟩
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `CauSeq.equiv_lim`：equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s)
· 使用定理 `CauSeq.mul_limZero_right`：mul_limZero_right (f : CauSeq β abv) {g} (hg :
 LimZero g) : LimZero (f * g) | ε, ε0 => let ⟨F, F0, hF⟩
-/
theorem lim_mul_lim (f g : CauSeq β abv) : lim f * lim g = lim (f * g) :=
  eq_lim_of_const_equiv <|
    show LimZero (const abv (lim f * lim g) - f * g) by
      have h :
        const abv (lim f * lim g) - f * g =
          (const abv (lim f) - f) * g + const abv (lim f) * (const abv (lim g) - g) := by
              apply Subtype.ext
              rw [coe_add]
              simp [sub_mul, mul_sub]
      rw [h]
      exact
        add_limZero (mul_limZero_left _ (Setoid.symm (equiv_lim _)))
          (mul_limZero_right _ (Setoid.symm (equiv_lim _)))
/-
**CauSeq.lim_mul** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：lim_mul (f : CauSeq β abv) (x : β) : lim f * x = lim (f * const abv x)
参数：f : CauSeq β abv；x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CauSeq.lim_mul_lim`：lim_mul_lim (f g : CauSeq β abv) : lim f * lim g = l
im (f * g)
· 使用定理 `CauSeq.lim_const`：lim_const (x : β) : lim (const abv x) = x
-/
theorem lim_mul (f : CauSeq β abv) (x : β) : lim f * x = lim (f * const abv x) := by
  rw [← lim_mul_lim, lim_const]
/-
**CauSeq.lim_neg** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：lim_neg (f : CauSeq β abv) : lim (-f) = -lim f
参数：f : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.lim_eq_of_equiv_const`：lim_eq_of_equiv_const {f : CauSeq β abv} {
x : β} (h : f ≈ CauSeq.const abv x) : lim f = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CauSeq.const_neg`：const_neg (x : β) : const (-x) = -const x
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `CauSeq.equiv_lim`：equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s)
-/
theorem lim_neg (f : CauSeq β abv) : lim (-f) = -lim f :=
  lim_eq_of_equiv_const
    (show LimZero (-f - const abv (-lim f)) by
      rw [const_neg, sub_neg_eq_add, add_comm, ← sub_eq_add_neg]
      exact Setoid.symm (equiv_lim f))
/-
**CauSeq.lim_sub** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：lim_sub (f g : CauSeq β abv) : lim f - lim g = lim (f - g)
参数：f g : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CauSeq.lim_neg`：lim_neg (f : CauSeq β abv) : lim (-f) = -lim f
· 使用定理 `CauSeq.lim_add`：lim_add (f g : CauSeq β abv) : lim f + lim g = lim (f + 
g)
-/
theorem lim_sub (f g : CauSeq β abv) : lim f - lim g = lim (f - g) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← lim_neg, lim_add f (-g)]
/-
**CauSeq.lim_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：lim_eq_zero_iff (f : CauSeq β abv) : lim f = 0 ↔ LimZero f
参数：f : CauSeq β abv。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.equiv_lim`：equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CauSeq.limZero_congr`：limZero_congr {f g : CauSeq β abv} (h : f ≈ g) : L
imZero f ↔ LimZero g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CauSeq.const_limZero`：const_limZero {x : β} : LimZero (const x) ↔ x = 0
· 使用定理 `CauSeq.ext`：ext {f g : CauSeq β abv} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CauSeq.lim_eq_of_equiv_const`：lim_eq_of_equiv_const {f : CauSeq β abv} {
x : β} (h : f ≈ CauSeq.const abv x) : lim f = x
-/
theorem lim_eq_zero_iff (f : CauSeq β abv) : lim f = 0 ↔ LimZero f :=
  ⟨fun h => by
    have hf := equiv_lim f
    rw [h] at hf
    exact (limZero_congr hf).mpr (const_limZero.mpr rfl),
   fun h => by
    have h₁ : f = f - const abv 0 := ext fun n => by simp
    rw [h₁] at h
    exact lim_eq_of_equiv_const h⟩

end

section

variable {β : Type*} [Field β] {abv : β → α} [IsAbsoluteValue abv] [IsComplete β abv]

/-
**CauSeq.lim_inv** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：lim_inv {f : CauSeq β abv} (hf : ¬LimZero f) : lim (inv f hf) = (lim f)⁻¹
参数：hf : ¬LimZero f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CauSeq.lim_eq_zero_iff`：lim_eq_zero_iff (f : CauSeq β abv) : lim f = 0 ↔
 LimZero f
· 使用定理 `CauSeq.lim_eq_of_equiv_const`：lim_eq_of_equiv_const {f : CauSeq β abv} {
x : β} (h : f ≈ CauSeq.const abv x) : lim f = x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `CauSeq.mul_limZero_right`：mul_limZero_right (f : CauSeq β abv) {g} (hg :
 LimZero g) : LimZero (f * g) | ε, ε0 => let ⟨F, F0, hF⟩
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `CauSeq.inv_mul_cancel`：inv_mul_cancel {f : CauSeq β abv} (hf) : inv f hf
 * f ≈ 1
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `sub_add_eq_sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a - (b + c) = a - b - c
· 使用定理 `sub_right_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c
 : α), a - b - c = a - c - b
· 使用定理 `CauSeq.sub_limZero`：sub_limZero {f g : CauSeq β abv} (hf : LimZero f) (h
g : LimZero g) : LimZero (f - g)
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `CauSeq.const_inv`：const_inv {x : β} (hx : x != 0) : const abv x⁻¹ = inv 
(const abv x) (by rwa [const_limZero])
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CauSeq.limZero_congr`：limZero_congr {f g : CauSeq β abv} (h : f ≈ g) : L
imZero f ↔ LimZero g
· 使用定理 `CauSeq.mul_limZero_left`：mul_limZero_left {f} (g : CauSeq β abv) (hg : L
imZero f) : LimZero (f * g) | ε, ε0 => let ⟨G, G0, hG⟩
· 使用定理 `CauSeq.equiv_lim`：equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s)
-/
theorem lim_inv {f : CauSeq β abv} (hf : ¬LimZero f) : lim (inv f hf) = (lim f)⁻¹ :=
  have hl : lim f ≠ 0 := by rwa [← lim_eq_zero_iff] at hf
  lim_eq_of_equiv_const <|
    show LimZero (inv f hf - const abv (lim f)⁻¹) from
      have h₁ : ∀ (g f : CauSeq β abv) (hf : ¬LimZero f), LimZero (g - f * inv f hf * g) :=
        fun g f hf => by
          have h₂ : g - f * inv f hf * g = 1 * g - f * inv f hf * g := by rw [one_mul g]
          have h₃ : f * inv f hf * g = (f * inv f hf) * g := by simp [mul_assoc]
          have h₄ : g - f * inv f hf * g = (1 - f * inv f hf) * g := by rw [h₂, h₃, ← sub_mul]
          have h₅ : g - f * inv f hf * g = g * (1 - f * inv f hf) := by rw [h₄, mul_comm]
          have h₆ : g - f * inv f hf * g = g * (1 - inv f hf * f) := by rw [h₅, mul_comm f]
          rw [h₆]; exact mul_limZero_right _ (Setoid.symm (CauSeq.inv_mul_cancel _))
      have h₂ :
        LimZero
          (inv f hf - const abv (lim f)⁻¹ -
            (const abv (lim f) - f) * (inv f hf * const abv (lim f)⁻¹)) := by
              rw [sub_mul, ← sub_add, sub_sub, sub_add_eq_sub_sub, sub_right_comm, sub_add]
              change LimZero
                (inv f hf - const abv (lim f) * (inv f hf * const abv (lim f)⁻¹) -
                  (const abv (lim f)⁻¹ - f * (inv f hf * const abv (lim f)⁻¹)))
              exact sub_limZero
                (by rw [← mul_assoc, mul_right_comm, const_inv hl]; exact h₁ _ _ _)
                (by rw [← mul_assoc]; exact h₁ _ _ _)
      (limZero_congr h₂).mpr <| mul_limZero_left _ (Setoid.symm (equiv_lim f))

end

section

variable [IsComplete α abs]

/-
**CauSeq.lim_le** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：lim_le {f : CauSeq α abs} {x : α} (h : f <= CauSeq.const abs x) : lim f <=
 x
参数：h : f <= CauSeq.const abs x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CauSeq.const_le`：const_le {x y : α} : const x <= const y ↔ x <= y
· 使用定理 `CauSeq.le_of_eq_of_le`：le_of_eq_of_le {f g h : CauSeq α abs} (hfg : f ≈ 
g) (hgh : g <= h) : f <= h
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `CauSeq.equiv_lim`：equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s)
-/
theorem lim_le {f : CauSeq α abs} {x : α} (h : f ≤ CauSeq.const abs x) : lim f ≤ x :=
  CauSeq.const_le.1 <| CauSeq.le_of_eq_of_le (Setoid.symm (equiv_lim f)) h
/-
**CauSeq.le_lim** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：le_lim {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x <= f) : x <= lim
 f
参数：h : CauSeq.const abs x <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CauSeq.const_le`：const_le {x y : α} : const x <= const y ↔ x <= y
· 使用定理 `CauSeq.le_of_le_of_eq`：le_of_le_of_eq {f g h : CauSeq α abs} (hfg : f <=
 g) (hgh : g ≈ h) : f <= h
· 使用定理 `CauSeq.equiv_lim`：equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s)
-/
theorem le_lim {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x ≤ f) : x ≤ lim f :=
  CauSeq.const_le.1 <| CauSeq.le_of_le_of_eq h (equiv_lim f)
/-
**CauSeq.lt_lim** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：lt_lim {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x < f) : x < lim f
参数：h : CauSeq.const abs x < f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CauSeq.const_lt`：const_lt {x y : α} : const x < const y ↔ x < y
· 使用定理 `CauSeq.lt_of_lt_of_eq`：lt_of_lt_of_eq {f g h : CauSeq α abs} (fg : f < g
) (gh : g ≈ h) : f < h
· 使用定理 `CauSeq.equiv_lim`：equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s)
-/
theorem lt_lim {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x < f) : x < lim f :=
  CauSeq.const_lt.1 <| CauSeq.lt_of_lt_of_eq h (equiv_lim f)
/-
**CauSeq.lim_lt** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：lim_lt {f : CauSeq α abs} {x : α} (h : f < CauSeq.const abs x) : lim f < x
参数：h : f < CauSeq.const abs x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CauSeq.const_lt`：const_lt {x y : α} : const x < const y ↔ x < y
· 使用定理 `CauSeq.lt_of_eq_of_lt`：lt_of_eq_of_lt {f g h : CauSeq α abs} (fg : f ≈ g
) (gh : g < h) : f < h
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `CauSeq.equiv_lim`：equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s)
-/
theorem lim_lt {f : CauSeq α abs} {x : α} (h : f < CauSeq.const abs x) : lim f < x :=
  CauSeq.const_lt.1 <| CauSeq.lt_of_eq_of_lt (Setoid.symm (equiv_lim f)) h

end

end CauSeq

