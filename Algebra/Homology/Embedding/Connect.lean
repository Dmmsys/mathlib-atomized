/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology

/-!
# Connecting a chain complex and a cochain complex

Given a chain complex `K`: `... ⟶ K.X 2 ⟶ K.X 1 ⟶ K.X 0`,
a cochain complex `L`: `L.X 0 ⟶ L.X 1 ⟶ L.X 2 ⟶ ...`,
a morphism `d₀ : K.X 0 ⟶ L.X 0` satisfying the identifies `K.d 1 0 ≫ d₀ = 0`
and `d₀ ≫ L.d 0 1 = 0`, we construct a cochain complex indexed by `ℤ` of the form
`... ⟶ K.X 2 ⟶ K.X 1 ⟶ K.X 0 ⟶ L.X 0 ⟶ L.X 1 ⟶ L.X 2 ⟶ ...`,
where `K.X 0` lies in degree `-1` and `L.X 0` in degree `0`.

## Main definitions

Say `K : ChainComplex C ℕ` and `L : CochainComplex C ℕ`, so `... ⟶ K₂ ⟶ K₁ ⟶ K₀`
and `L⁰ ⟶ L¹ ⟶ L² ⟶ ...`.

* `ConnectData K L`: an auxiliary structure consisting of `d₀ : K₀ ⟶ L⁰` "connecting" the
  complexes and proofs that the induced maps `K₁ ⟶ K₀ ⟶ L⁰` and `K₀ ⟶ L⁰ ⟶ L¹` are both zero.

Now say `h : ConnectData K L`.

* `CochainComplex.ConnectData.cochainComplex h` : the induced ℤ-indexed complex
  `... ⟶ K₁ ⟶ K₀ ⟶ L⁰ ⟶ L¹ ⟶ ...`
* `CochainComplex.ConnectData.homologyIsoPos h (n : ℕ) (m : ℤ)` : if `m = n + 1`,
  the isomorphism `h.cochainComplex.homology m ≅ L.homology (n + 1)`
* `CochainComplex.ConnectData.homologyIsoNeg h (n : ℕ) (m : ℤ)` : if `m = -(n + 2)`,
  the isomorphism `h.cochainComplex.homology m ≅ K.homology (n + 1)`

## TODO

* Computation of `h.cochainComplex.homology k` when `k = 0` or `k = -1`.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace CochainComplex

variable {K K' K'' : ChainComplex C ℕ} {L L' L'' : CochainComplex C ℕ}

variable (K L) in
/-- Given `K : ChainComplex C ℕ` and `L : CochainComplex C ℕ`, this data
allows to connect `K` and `L` in order to get a cochain complex indexed by `ℤ`,
see `ConnectData.cochainComplex`. -/
/-
**CochainComplex.ConnectData** 是 Mathlib 中的一个归纳类型，位于命名空间 `CochainComplex`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] → ChainComplex C ℕ → CochainComplex C
 ℕ → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `K : ChainComplex C ℕ` and `L : CochainComplex C ℕ`, this data
allows to connect `K` and `L` in order to get a cochain complex indexed by `ℤ`,
see `ConnectData.cochainComplex`.
-/
structure ConnectData where
  /-- the differential which connect `K` and `L` -/
  d₀ : K.X 0 ⟶ L.X 0
  comp_d₀ : K.d 1 0 ≫ d₀ = 0
  d₀_comp : d₀ ≫ L.d 0 1 = 0

namespace ConnectData

attribute [reassoc (attr := simp)] comp_d₀ d₀_comp

variable (h : ConnectData K L) (h' : ConnectData K' L') (h'' : ConnectData K'' L'')

variable (K L) in
/-- Auxiliary definition for `ConnectData.cochainComplex`. -/
/-
**CochainComplex.ConnectData.X** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.Connect
Data`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] → ChainComplex C ℕ → CochainComplex C
 ℕ → ℤ → C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `ConnectData.cochainComplex`.
-/
def X : ℤ → C
  | .ofNat n => L.X n
  | .negSucc n => K.X n
/-
**CochainComplex.ConnectData.X_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex.C
onnectData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {K : ChainComplex C ℕ} {L : CochainComplex 
C ℕ} (n : ℕ), CochainComplex.ConnectData.X K L ↑n = L.X n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma X_ofNat (n : ℕ) : X K L n = L.X n := rfl
/-
**CochainComplex.ConnectData.X_negSucc** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex
.ConnectData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {K : ChainComplex C ℕ} {L : CochainComplex 
C ℕ} (n : ℕ), CochainComplex.ConnectData.X K L (Int.negSucc n) = K.X n
参数：n : ℕ；Int.negSucc n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma X_negSucc (n : ℕ) : X K L (.negSucc n) = K.X n := rfl
/-
**CochainComplex.ConnectData.X_zero** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex.Co
nnectData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {K : ChainComplex C ℕ} {L : CochainComplex 
C ℕ}, CochainComplex.ConnectData.X K L 0 = L.X 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma X_zero : X K L 0 = L.X 0 := rfl
/-
**CochainComplex.ConnectData.X_negOne** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex.
ConnectData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {K : ChainComplex C ℕ} {L : CochainComplex 
C ℕ}, CochainComplex.ConnectData.X K L (-1) = K.X 0
参数：-1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma X_negOne : X K L (-1) = K.X 0 := rfl

/-- Auxiliary definition for `ConnectData.cochainComplex`. -/
/-
**CochainComplex.ConnectData.d** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.Connect
Data`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {K : ChainComplex C ℕ} →     
    {L : CochainComplex C ℕ} →           CochainComplex.ConnectData K L →       
      (n m : ℤ) → CochainComplex.ConnectData.X K L n ⟶ CochainComplex.ConnectDat
a.X K L m
参数：n m : ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `ConnectData.cochainComplex`.
-/
def d : ∀ (n m : ℤ), X K L n ⟶ X K L m
  | .ofNat n, .ofNat m => L.d n m
  | .negSucc n, .negSucc m => K.d n m
  | .negSucc 0, .ofNat 0 => h.d₀
  | .ofNat _, .negSucc _ => 0
  | .negSucc _, .ofNat _ => 0
/-
**CochainComplex.ConnectData.d_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex.C
onnectData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {K : ChainComplex C ℕ} {L : CochainComplex 
C ℕ} (h : CochainComplex.ConnectData K L) (n m : ℕ), h.d ↑n ↑m = L.d n m
参数：h : CochainComplex.ConnectData K L；n m : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma d_ofNat (n m : ℕ) : h.d n m = L.d n m := rfl
/-
**CochainComplex.ConnectData.d_negSucc** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex
.ConnectData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {K : ChainComplex C ℕ} {L : CochainComplex 
C ℕ} (h : CochainComplex.ConnectData K L) (n m : ℕ),   h.d (Int.negSucc n) (Int.
negSucc m) = K.d n m
参数：h : CochainComplex.ConnectData K L；n m : ℕ；Int.negSucc n；Int.negSucc m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma d_negSucc (n m : ℕ) : h.d (.negSucc n) (.negSucc m) = K.d n m := by simp [d]
/-
**CochainComplex.ConnectData.d_sub_one_zero** 是 Mathlib 中的一个定理，位于命名空间 `CochainCo
mplex.ConnectData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {K : ChainComplex C ℕ} {L : CochainComplex 
C ℕ} (h : CochainComplex.ConnectData K L), h.d (-1) 0 = h.d₀
参数：h : CochainComplex.ConnectData K L；-1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma d_sub_one_zero : h.d (-1) 0 = h.d₀ := rfl
/-
**CochainComplex.ConnectData.d_zero_one** 是 Mathlib 中的一个定理，位于命名空间 `CochainComple
x.ConnectData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {K : ChainComplex C ℕ} {L : CochainComplex 
C ℕ} (h : CochainComplex.ConnectData K L), h.d 0 1 = L.d 0 1
参数：h : CochainComplex.ConnectData K L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma d_zero_one : h.d 0 1 = L.d 0 1 := rfl
/-
**CochainComplex.ConnectData.d_sub_two_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Cochai
nComplex.ConnectData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {K : ChainComplex C ℕ} {L : CochainComplex 
C ℕ} (h : CochainComplex.ConnectData K L), h.d (-2) (-1) = K.d 1 0
参数：h : CochainComplex.ConnectData K L；-2；-1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma d_sub_two_sub_one : h.d (-2) (-1) = K.d 1 0 := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CochainComplex.ConnectData.shape** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.Con
nectData`。
形式化陈述：shape (n m : Int) (hnm : n + 1 != m) : h.d n m = 0
参数：n m : Int；hnm : n + 1 != m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ComplexShape.up_Rel`：∀ (α : Type u_2) [inst : Add α] [inst_1 : IsRightCa
ncelAdd α] [inst_2 : One α] (i j : α),   (ComplexShape.up α).Rel i j = (i + 1 = 
j)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CochainComplex.ConnectData.d_negSucc`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {K 
: ChainComplex C ℕ} {L : C…
· 使用定理 `ComplexShape.down_Rel`：∀ (α : Type u_2) [inst : Add α] [inst_1 : IsRight
CancelAdd α] [inst_2 : One α] (i j : α),   (ComplexShape.down α).Rel i j = (j + 
1 = i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `_private.Mathlib.Algebra.Homology.Embedding.Connect.0.CochainComplex.Con
nectData.d.match_1.eq_5`：∀ (motive : ℤ → ℤ → Sort u_1) (a a_1 : ℕ) (h_1 : (n m :
 ℕ) → motive (Int.ofNat n) (Int.ofNat m))   (h_2 : (n m : ℕ) → motive (Int.negSu
cc n)…
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma shape (n m : ℤ) (hnm : n + 1 ≠ m) : h.d n m = 0 :=
  match n, m with
  | .ofNat n, .ofNat m => L.shape _ _ (by simp at hnm ⊢; lia)
  | .negSucc n, .negSucc m => by
    simpa only [d_negSucc] using! K.shape n m (by simp at hnm ⊢; lia)
  | .negSucc 0, .ofNat 0 => by simp at hnm
  | .ofNat _, .negSucc m => rfl
  | .negSucc n, .ofNat m => by
    obtain _ | n := n
    · obtain _ | m := m
      · simp at hnm
      · rfl
    · simp only [d]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.ConnectData.d_comp_d** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.
ConnectData`。
形式化陈述：d_comp_d (n m p : Int) : h.d n m ≫ h.d m p = 0
参数：n m p : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `CochainComplex.ConnectData.d₀_comp`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {K : 
ChainComplex C ℕ} {L : C…
· 使用定理 `CochainComplex.ConnectData.comp_d₀`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {K : 
ChainComplex C ℕ} {L : C…
· 使用定理 `CochainComplex.ConnectData.d_negSucc`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {K 
: ChainComplex C ℕ} {L : C…
· 使用引理 `CochainComplex.ConnectData.shape`：shape (n m : Int) (hnm : n + 1 != m) :
 h.d n m = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
lemma d_comp_d (n m p : ℤ) : h.d n m ≫ h.d m p = 0 := by
  by_cases hnm : n + 1 = m; swap
  · rw [h.shape n m hnm, zero_comp]
  by_cases hmp : m + 1 = p; swap
  · rw [h.shape m p hmp, comp_zero]
  obtain n | (_ | _ | n) := n
  · obtain rfl : m = .ofNat (n + 1) := by simp [← hnm]
    obtain rfl : p = .ofNat (n + 2) := by simp [← hmp]; lia
    simp only [Int.ofNat_eq_natCast, X_ofNat, d_ofNat, HomologicalComplex.d_comp_d]
  · obtain rfl : m = 0 := by lia
    obtain rfl : p = 1 := by lia
    simp
  · obtain rfl : m = -1 := by lia
    obtain rfl : p = 0 := by lia
    simp
  · obtain rfl : m = .negSucc (n + 1) := by lia
    obtain rfl : p = .negSucc n := by lia
    simp

/-- Given `h : ConnectData K L` where `K : ChainComplex C ℕ` and `L : CochainComplex C ℕ`,
this is the cochain complex indexed by `ℤ` obtained by connecting `K` and `L`:
`... ⟶ K.X 2 ⟶ K.X 1 ⟶ K.X 0 ⟶ L.X 0 ⟶ L.X 1 ⟶ L.X 2 ⟶ ...`. -/
@[simps]
/-
**CochainComplex.ConnectData.cochainComplex** 是 Mathlib 中的一个定义，位于命名空间 `CochainCo
mplex.ConnectData`。
形式化陈述：cochainComplex : CochainComplex C Int where X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.ConnectData.shape`：shape (n m : Int) (hnm : n + 1 != m) :
 h.d n m = 0

--- 原说明 ---
Given `h : ConnectData K L` where `K : ChainComplex C ℕ` and `L : CochainComplex
 C ℕ`,
this is the cochain complex indexed by `ℤ` obtained by connecting `K` and `L`:
`... ⟶ K.X 2 ⟶ K.X 1 ⟶ K.X 0 ⟶ L.X 0 ⟶ L.X 1 ⟶ L.X 2 ⟶ ...`.
-/
def cochainComplex : CochainComplex C ℤ where
  X := X K L
  d := h.d
  shape := h.shape

open HomologicalComplex

set_option backward.isDefEq.respectTransparency false in
/-- If `h : ConnectData K L`, then `h.cochainComplex` identifies to `L` in degrees `≥ 0`. -/
@[simps!]
/-
**CochainComplex.ConnectData.restrictionGEIso** 是 Mathlib 中的一个定义，位于命名空间 `Cochain
Complex.ConnectData`。
形式化陈述：restrictionGEIso : h.cochainComplex.restriction (ComplexShape.embeddingUpI
ntGE 0) ≅ L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `h : ConnectData K L`, then `h.cochainComplex` identifies to `L` in degrees `
≥ 0`.
-/
def restrictionGEIso :
    h.cochainComplex.restriction (ComplexShape.embeddingUpIntGE 0) ≅ L :=
  Hom.isoOfComponents
    (fun n ↦ h.cochainComplex.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
      (i := n) (i' := n) (by simp)) (by
    rintro n _ rfl
    rw [restriction_d_eq (e := (ComplexShape.embeddingUpIntGE 0)) _ (i' := n)
      (j' := (n + 1 : ℕ)) (by simp) (by simp), cochainComplex_d, h.d_ofNat]
    simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `h : ConnectData K L`, then `h.cochainComplex` identifies to `K` in degrees `≤ -1`. -/
@[simps!]
/-
**CochainComplex.ConnectData.restrictionLEIso** 是 Mathlib 中的一个定义，位于命名空间 `Cochain
Complex.ConnectData`。
形式化陈述：restrictionLEIso : h.cochainComplex.restriction (ComplexShape.embeddingUpI
ntLE (-1)) ≅ K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `h : ConnectData K L`, then `h.cochainComplex` identifies to `K` in degrees `
≤ -1`.
-/
def restrictionLEIso :
    h.cochainComplex.restriction (ComplexShape.embeddingUpIntLE (-1)) ≅ K :=
  Hom.isoOfComponents
    (fun n ↦ h.cochainComplex.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
        (i := n) (i' := .negSucc n) (by dsimp; lia)) (by
    rintro _ n rfl
    rw [restriction_d_eq (e := (ComplexShape.embeddingUpIntLE (-1))) _
      (i' := Int.negSucc (n + 1)) (j' := Int.negSucc n) (by dsimp; lia) (by dsimp; lia),
      cochainComplex_d, d_negSucc]
    simp)

/-- Given `h : ConnectData K L` and `n : ℕ` non-zero, the homology
of `h.cochainComplex` in degree `n` identifies to the homology of `L` in degree `n`. -/
/-
**CochainComplex.ConnectData.homologyIsoPos** 是 Mathlib 中的一个定义，位于命名空间 `CochainCo
mplex.ConnectData`。
形式化陈述：homologyIsoPos (n : Nat) [NeZero n] (m : Int) (hm : m = n) [h.cochainCompl
ex.HasHomology m] [L.HasHomology n] : h.cochainComplex.homology m ≅ L.homology n
参数：n : Nat；m : Int；hm : m = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `h : ConnectData K L` and `n : ℕ` non-zero, the homology
of `h.cochainComplex` in degree `n` identifies to the homology of `L` in degree 
`n`.
-/
noncomputable def homologyIsoPos (n : ℕ) [NeZero n] (m : ℤ) (hm : m = n)
    [h.cochainComplex.HasHomology m] [L.HasHomology n] :
    h.cochainComplex.homology m ≅ L.homology n :=
  have := hasHomology_of_iso h.restrictionGEIso.symm n
  (h.cochainComplex.restrictionHomologyIso
    (ComplexShape.embeddingUpIntGE 0) (n - 1) n (n + 1) (by cases n <;> simp) (by simp)
      (i' := m - 1) (j' := m) (k' := m + 1) (by have := NeZero.ne n; cases n <;> simp <;> lia)
      (by simp; lia) (by simp; lia) (by simp) (by simp)).symm ≪≫
    HomologicalComplex.homologyMapIso h.restrictionGEIso n

/-- Given `h : ConnectData K L` and `n : ℕ` non-zero, the homology
of `h.cochainComplex` in degree `-(n + 1)` identifies to the homology of `K` in degree `n`. -/
/-
**CochainComplex.ConnectData.homologyIsoNeg** 是 Mathlib 中的一个定义，位于命名空间 `CochainCo
mplex.ConnectData`。
形式化陈述：homologyIsoNeg (n : Nat) [NeZero n] (m : Int) (hm : m = -(n + 1 : Nat)) [h
.cochainComplex.HasHomology m] [K.HasHomology n] : h.cochainComplex.homology m ≅
 K.homology n
参数：n : Nat；m : Int；hm : m = -(n + 1 : Nat)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `h : ConnectData K L` and `n : ℕ` non-zero, the homology
of `h.cochainComplex` in degree `-(n + 1)` identifies to the homology of `K` in 
degree `n`.
-/
noncomputable def homologyIsoNeg (n : ℕ) [NeZero n] (m : ℤ) (hm : m = -(n + 1 : ℕ))
    [h.cochainComplex.HasHomology m] [K.HasHomology n] :
    h.cochainComplex.homology m ≅ K.homology n :=
  have := hasHomology_of_iso h.restrictionLEIso.symm n
  (h.cochainComplex.restrictionHomologyIso
    (ComplexShape.embeddingUpIntLE (-1)) (n + 1) n (n - 1) (by simp) (by cases n <;> simp)
      (i' := m - 1) (j' := m) (k' := m + 1) (by simp; lia) (by simp; lia)
      (by have := NeZero.ne n; cases n <;> simp <;> lia) (by simp) (by simp)).symm ≪≫
    HomologicalComplex.homologyMapIso h.restrictionLEIso n

variable
  (fK : K ⟶ K') (fL : L ⟶ L') (f_comm : fK.f 0 ≫ h'.d₀ = h.d₀ ≫ fL.f 0)
  (fK' : K' ⟶ K'') (fL' : L' ⟶ L'') (f_comm' : fK'.f 0 ≫ h''.d₀ = h'.d₀ ≫ fL'.f 0)

/-- Connecting complexes is functorial. -/
@[simps]
/-
**CochainComplex.ConnectData.map** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.Conne
ctData`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {K K' : ChainComplex C ℕ} →  
       {L L' : CochainComplex C ℕ} →           (h : CochainComplex.ConnectData K
 L) →             (h' : CochainComplex.ConnectData K' L') →               (fK : 
K ⟶ K') →                 (fL : L ⟶ L') →                   CategoryTheory.Categ
oryStruct.comp (fK.f 0) h'.d₀ = CategoryTheory.CategoryStruct.comp h.d₀ (fL.f 0)
 →                     (h.cochainComplex ⟶ h'.cochainComplex)
参数：h : CochainComplex.ConnectData K L；h' : CochainComplex.ConnectData K' L'；fK :
 K ⟶ K'；fL : L ⟶ L'；fK.f 0；fL.f 0；h.cochainComplex ⟶ h'.cochainComplex。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Connecting complexes is functorial.
-/
protected def map : h.cochainComplex ⟶ h'.cochainComplex where
  f
  | .ofNat n => fL.f n
  | .negSucc n => fK.f n
  comm'
  | .ofNat i, _, .refl _ => fL.comm _ _
  | .negSucc 0, _, .refl _ => by simpa
  | .negSucc (i + 1), _, .refl _ => fK.comm _ _

set_option backward.defeqAttrib.useBackward true in
/-
**CochainComplex.ConnectData.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex.Co
nnectData`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {K : ChainComplex C ℕ} {L : CochainComplex 
C ℕ} (h : CochainComplex.ConnectData K L),   h.map h (CategoryTheory.CategoryStr
uct.id K) (CategoryTheory.CategoryStruct.id L) ⋯ =     CategoryTheory.CategorySt
ruct.id h.cochainComplex
参数：h : CochainComplex.ConnectData K L；CategoryTheory.CategoryStruct.id K；Categor
yTheory.CategoryStruct.id L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_id : h.map h (𝟙 K) (𝟙 L) (by simp) = 𝟙 _ := by ext (m | _ | m) <;> simp; rfl

set_option backward.defeqAttrib.useBackward true in
/-
**CochainComplex.ConnectData.map_comp_map** 是 Mathlib 中的一个引理，位于命名空间 `CochainComp
lex.ConnectData`。
形式化陈述：map_comp_map : h.map h' fK fL f_comm ≫ h'.map h'' fK' fL' f_comm' = h.map 
h'' (fK ≫ fK') (fL ≫ fL') (by simp [f_comm', reassoc_of% f_comm])
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp_map :
    h.map h' fK fL f_comm ≫ h'.map h'' fK' fL' f_comm'
     = h.map h'' (fK ≫ fK') (fL ≫ fL') (by simp [f_comm', reassoc_of% f_comm]) := by
  ext (m | _ | m) <;> simp; rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.ConnectData.homologyMap_map_of_eq_succ** 是 Mathlib 中的一个引理，位于命名空
间 `CochainComplex.ConnectData`。
形式化陈述：homologyMap_map_of_eq_succ (n : Nat) [NeZero n] (m : Int) (hmn : m = n) [H
asHomology h.cochainComplex m] [HasHomology L n] [HasHomology h'.cochainComplex 
m] [HasHomology L' n] : homologyMap (h.map h' fK fL f_comm) m = (h.homologyIsoPo
s n m hmn).hom ≫ homologyMap fL n ≫ (h'.homologyIsoPos n m hmn).inv
参数：n : Nat；m : Int；hmn : m = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `HomologicalComplex.instMonoHomologyι`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
   {ι : Type u_2} {c : Com…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `HomologicalComplex.homologyι_naturality`：homologyι_naturality : homology
Map φ i ≫ L.homologyι i = K.homologyι i ≫ opcyclesMap φ i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomologicalComplex.restrictionHomologyIso_hom_homologyι`：restrictionHomo
logyIso_hom_homologyι : (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi''
 hk'').hom ≫ K.homologyι j' = (K.restriction …
· 使用定理 `HomologicalComplex.homologyι_naturality_assoc`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {ι : Type u_2} {c : Com…
· 使用定理 `HomologicalComplex.restrictionHomologyIso_inv_homologyι_assoc`：∀ {ι : Ty
pe u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_
3}   [inst : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `HomologicalComplex.instEpiPOpcycles`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `HomologicalComplex.p_opcyclesMap`：p_opcyclesMap : K.pOpcycles i ≫ opcycl
esMap φ i = φ.f i ≫ L.pOpcycles i
· 使用定理 `HomologicalComplex.pOpcycles_restrictionOpcyclesIso_inv_assoc`：∀ {ι : Ty
pe u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_
3}   [inst : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `HomologicalComplex.p_opcyclesMap_assoc`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.pOpcycles_restrictionOpcyclesIso_hom`：pOpcycles_restr
ictionOpcyclesIso_hom : (K.restriction e).pOpcycles j ≫ (K.restrictionOpcyclesIs
o e i j hi hi' hj' hi'').hom = (K.restriction…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homologyMap_map_of_eq_succ (n : ℕ) [NeZero n] (m : ℤ) (hmn : m = n)
    [HasHomology h.cochainComplex m] [HasHomology L n]
    [HasHomology h'.cochainComplex m] [HasHomology L' n] :
    homologyMap (h.map h' fK fL f_comm) m =
    (h.homologyIsoPos n m hmn).hom ≫ homologyMap fL n ≫ (h'.homologyIsoPos n m hmn).inv := by
  rw [← cancel_mono (HomologicalComplex.homologyι ..)]
  dsimp [homologyIsoPos]
  simp only [homologyι_naturality, Category.assoc, restrictionHomologyIso_hom_homologyι,
    homologyι_naturality_assoc, restrictionHomologyIso_inv_homologyι_assoc]
  congr 1
  rw [← cancel_epi (HomologicalComplex.pOpcycles ..)]
  subst hmn
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.ConnectData.homologyMap_map_of_eq_neg_succ** 是 Mathlib 中的一个引理，位
于命名空间 `CochainComplex.ConnectData`。
形式化陈述：homologyMap_map_of_eq_neg_succ (n : Nat) [NeZero n] (m : Int) (hmn : m = -
↑(n + 1)) [HasHomology h.cochainComplex m] [HasHomology K n] [HasHomology h'.coc
hainComplex m] [HasHomology K' n] : homologyMap (h.map h' fK fL f_comm) m = (h.h
omologyIsoNeg n m hmn).hom ≫ homologyMap fK n ≫ (h'.homologyIsoNeg n m hmn).inv
参数：n : Nat；m : Int；hmn : m = -↑(n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `HomologicalComplex.instMonoHomologyι`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
   {ι : Type u_2} {c : Com…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `HomologicalComplex.homologyι_naturality`：homologyι_naturality : homology
Map φ i ≫ L.homologyι i = K.homologyι i ≫ opcyclesMap φ i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomologicalComplex.restrictionHomologyIso_hom_homologyι`：restrictionHomo
logyIso_hom_homologyι : (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi''
 hk'').hom ≫ K.homologyι j' = (K.restriction …
· 使用定理 `HomologicalComplex.homologyι_naturality_assoc`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {ι : Type u_2} {c : Com…
· 使用定理 `HomologicalComplex.restrictionHomologyIso_inv_homologyι_assoc`：∀ {ι : Ty
pe u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_
3}   [inst : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `HomologicalComplex.instEpiPOpcycles`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `HomologicalComplex.p_opcyclesMap`：p_opcyclesMap : K.pOpcycles i ≫ opcycl
esMap φ i = φ.f i ≫ L.pOpcycles i
· 使用定理 `HomologicalComplex.pOpcycles_restrictionOpcyclesIso_inv_assoc`：∀ {ι : Ty
pe u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_
3}   [inst : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `HomologicalComplex.p_opcyclesMap_assoc`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.pOpcycles_restrictionOpcyclesIso_hom`：pOpcycles_restr
ictionOpcyclesIso_hom : (K.restriction e).pOpcycles j ≫ (K.restrictionOpcyclesIs
o e i j hi hi' hj' hi'').hom = (K.restriction…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homologyMap_map_of_eq_neg_succ (n : ℕ) [NeZero n] (m : ℤ) (hmn : m = -↑(n + 1))
    [HasHomology h.cochainComplex m] [HasHomology K n]
    [HasHomology h'.cochainComplex m] [HasHomology K' n] :
    homologyMap (h.map h' fK fL f_comm) m =
      (h.homologyIsoNeg n m hmn).hom ≫ homologyMap fK n ≫ (h'.homologyIsoNeg n m hmn).inv := by
  rw [← cancel_mono (HomologicalComplex.homologyι ..)]
  dsimp [homologyIsoNeg]
  simp only [homologyι_naturality, Category.assoc, restrictionHomologyIso_hom_homologyι,
    homologyι_naturality_assoc, restrictionHomologyIso_inv_homologyι_assoc]
  congr 1
  rw [← cancel_epi (HomologicalComplex.pOpcycles ..)]
  obtain rfl : m = .negSucc n := hmn
  simp

end ConnectData

end CochainComplex

