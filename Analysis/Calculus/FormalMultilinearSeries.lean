/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Formal multilinear series

In this file we define `FormalMultilinearSeries 𝕜 E F` to be a family of `n`-multilinear maps for
all `n`, designed to model the sequence of derivatives of a function. In other files we use this
notion to define `C^n` functions (called `contDiff` in `mathlib`) and analytic functions.

## Notation

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

## Tags

multilinear, formal series
-/

@[expose] public section


noncomputable section

open Set Fin Topology

universe u u' v w x y
variable {𝕜 : Type u} {𝕜' : Type u'} {E : Type v} {F : Type w} {G : Type x} {H : Type y}

section

variable [Semiring 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F] [ContinuousConstSMul 𝕜 F]
  [AddCommMonoid G] [Module 𝕜 G] [TopologicalSpace G] [ContinuousAdd G] [ContinuousConstSMul 𝕜 G]
  [AddCommMonoid H] [Module 𝕜 H] [TopologicalSpace H] [ContinuousAdd H] [ContinuousConstSMul 𝕜 H]

/-- A formal multilinear series over a field `𝕜`, from `E` to `F`, is given by a family of
multilinear maps from `E^n` to `F` for all `n`. -/
@[nolint unusedArguments]
/-
**FormalMultilinearSeries** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FormalMultilinearSeries (𝕜 : Type*) (E : Type*) (F : Type*) [Semiring 𝕜] [
AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E] [Continuous
ConstSMul 𝕜 E] [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAd
d F] [ContinuousConstSMul 𝕜 F]
参数：𝕜 : Type*；E : Type*；F : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A formal multilinear series over a field `𝕜`, from `E` to `F`, is given by a fam
ily of
multilinear maps from `E^n` to `F` for all `n`.
-/
def FormalMultilinearSeries (𝕜 : Type*) (E : Type*) (F : Type*) [Semiring 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F]
    [ContinuousConstSMul 𝕜 F] :=
  ∀ n : ℕ, E [×n]→L[𝕜] F
deriving Inhabited

-- This instance exists to avoid an nsmul diamond.
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (𝕜') [Semiring 𝕜'] [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [SMulCommClass 𝕜 𝕜' F] :
    SMul 𝕜' (FormalMultilinearSeries 𝕜 E F) where
  smul k x n := k • x n

section AddCommMonoid

/-- Copy `Pi.addCommMonoid`, ensuring the pointwise operations hold by defeq. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy `Pi.addCommMonoid`, ensuring the pointwise operations hold by defeq.
-/
instance : AddCommMonoid (FormalMultilinearSeries 𝕜 E F) := fast_instance% {
  __ := Pi.addCommMonoid
  zero _ := 0
  add x y n := x n + y n }

end AddCommMonoid

section Module

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (𝕜') [Semiring 𝕜'] [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [SMulCommClass 𝕜 𝕜' F] :
    Module 𝕜' (FormalMultilinearSeries 𝕜 E F) :=
  inferInstanceAs <| Module 𝕜' <| ∀ n : ℕ, E [×n]→L[𝕜] F

end Module

namespace FormalMultilinearSeries

@[simp]
/-
**FormalMultilinearSeries.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinea
rSeries`。
形式化陈述：zero_apply (n : Nat) : (0 : FormalMultilinearSeries 𝕜 E F) n = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (n : ℕ) : (0 : FormalMultilinearSeries 𝕜 E F) n = 0 := rfl

@[simp]
/-
**FormalMultilinearSeries.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinear
Series`。
形式化陈述：add_apply (p q : FormalMultilinearSeries 𝕜 E F) (n : Nat) : (p + q) n = p 
n + q n
参数：p q : FormalMultilinearSeries 𝕜 E F；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply (p q : FormalMultilinearSeries 𝕜 E F) (n : ℕ) : (p + q) n = p n + q n := rfl

@[simp]
/-
**FormalMultilinearSeries.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinea
rSeries`。
形式化陈述：smul_apply [Semiring 𝕜'] [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [SMulCom
mClass 𝕜 𝕜' F] (f : FormalMultilinearSeries 𝕜 E F) (n : Nat) (a : 𝕜') : (a • f) 
n = a • f n
参数：f : FormalMultilinearSeries 𝕜 E F；n : Nat；a : 𝕜'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply [Semiring 𝕜'] [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [SMulCommClass 𝕜 𝕜' F]
    (f : FormalMultilinearSeries 𝕜 E F) (n : ℕ) (a : 𝕜') : (a • f) n = a • f n := rfl

@[ext]
/-
**FormalMultilinearSeries.ext** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinearSeries
`。
形式化陈述：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [inst : Semiring 𝕜] [inst_1 : Add
CommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : TopologicalSpace E] [inst
_4 : ContinuousAdd E] [inst_5 : ContinuousConstSMul 𝕜 E] [inst_6 : AddCommMonoid
 F]   [inst_7 : _root_.Module 𝕜 F] [inst_8 : TopologicalSpace F] [inst_9 : Conti
nuousAdd F]   [inst_10 : ContinuousConstSMul 𝕜 F] {p q : FormalMultilinearSeries
 𝕜 E F}, (∀ (n : ℕ), p n = q n) → p = q
参数：∀ (n : ℕ), p n = q n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
protected theorem ext {p q : FormalMultilinearSeries 𝕜 E F} (h : ∀ n, p n = q n) : p = q :=
  funext h
/-
**FormalMultilinearSeries.ne_iff** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinearSer
ies`。
形式化陈述：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [inst : Semiring 𝕜] [inst_1 : Add
CommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : TopologicalSpace E] [inst
_4 : ContinuousAdd E] [inst_5 : ContinuousConstSMul 𝕜 E] [inst_6 : AddCommMonoid
 F]   [inst_7 : _root_.Module 𝕜 F] [inst_8 : TopologicalSpace F] [inst_9 : Conti
nuousAdd F]   [inst_10 : ContinuousConstSMul 𝕜 F] {p q : FormalMultilinearSeries
 𝕜 E F}, p ≠ q ↔ ∃ n, p n ≠ q n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
-/
protected theorem ne_iff {p q : FormalMultilinearSeries 𝕜 E F} : p ≠ q ↔ ∃ n, p n ≠ q n :=
  Function.ne_iff

/-- Cartesian product of two formal multilinear series (with the same field `𝕜` and the same source
space, but possibly different target spaces). -/
/-
**FormalMultilinearSeries.prod** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilinearSerie
s`。
形式化陈述：{𝕜 : Type u} →   {E : Type v} →     {F : Type w} →       {G : Type x} →   
      [inst : Semiring 𝕜] →           [inst_1 : AddCommMonoid E] →             [
inst_2 : _root_.Module 𝕜 E] →               [inst_3 : TopologicalSpace E] →     
            [inst_4 : ContinuousAdd E] →                   [inst_5 : ContinuousC
onstSMul 𝕜 E] →                     [inst_6 : AddCommMonoid F] →                
       [inst_7 : _root_.Module 𝕜 F] →                         [inst_8 : Topologi
calSpace F] →                           [inst_9 : ContinuousAdd F] →            
                 [inst_10 : ContinuousConstSMul 𝕜 F] →                          
     [inst_11 : AddCommMonoid G] →                                 [inst_12 : _r
oot_.Module 𝕜 G] →                                   [inst_13 : TopologicalSpace
 G] →                                     [inst_14 : ContinuousAdd G] →         
                              [inst_15 : ContinuousConstSMul 𝕜 G] →             
                            FormalMultilinearSeries 𝕜 E F →                     
                      FormalMultilinearSeries 𝕜 E G → FormalMultilinearSeries 𝕜 
E (F × G)
参数：F × G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cartesian product of two formal multilinear series (with the same field `𝕜` and 
the same source
space, but possibly different target spaces).
-/
def prod (p : FormalMultilinearSeries 𝕜 E F) (q : FormalMultilinearSeries 𝕜 E G) :
    FormalMultilinearSeries 𝕜 E (F × G)
  | n => (p n).prod (q n)

/-- Product of formal multilinear series (with the same field `𝕜` and the same source
space, but possibly different target spaces). -/
/-
**FormalMultilinearSeries.pi** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilinearSeries`
。
形式化陈述：{𝕜 : Type u} →   {E : Type v} →     [inst : Semiring 𝕜] →       [inst_1 : 
AddCommMonoid E] →         [inst_2 : _root_.Module 𝕜 E] →           [inst_3 : To
pologicalSpace E] →             [inst_4 : ContinuousAdd E] →               [inst
_5 : ContinuousConstSMul 𝕜 E] →                 {ι : Type u_1} →                
   {F : ι → Type u_2} →                     [inst_6 : (i : ι) → AddCommGroup (F 
i)] →                       [inst_7 : (i : ι) → _root_.Module 𝕜 (F i)] →        
                 [inst_8 : (i : ι) → TopologicalSpace (F i)] →                  
         [inst_9 : ∀ (i : ι), IsTopologicalAddGroup (F i)] →                    
         [inst_10 : ∀ (i : ι), ContinuousConstSMul 𝕜 (F i)] →                   
            ((i : ι) → FormalMultilinearSeries 𝕜 E (F i)) →                     
            FormalMultilinearSeries 𝕜 E ((i : ι) → F i)
参数：i : ι；F i；i : ι；F i；i : ι；F i；i : ι；F i；i : ι；F i；(i : ι) → FormalMultilinear
Series 𝕜 E (F i)；(i : ι) → F i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of formal multilinear series (with the same field `𝕜` and the same sourc
e
space, but possibly different target spaces).
-/
@[simp] def pi {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)] [∀ i, TopologicalSpace (F i)]
    [∀ i, IsTopologicalAddGroup (F i)] [∀ i, ContinuousConstSMul 𝕜 (F i)]
    (p : Π i, FormalMultilinearSeries 𝕜 E (F i)) :
    FormalMultilinearSeries 𝕜 E (Π i, F i)
  | n => ContinuousMultilinearMap.pi (fun i ↦ p i n)

/-- Killing the zeroth coefficient in a formal multilinear series -/
/-
**FormalMultilinearSeries.removeZero** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilinea
rSeries`。
形式化陈述：{𝕜 : Type u} →   {E : Type v} →     {F : Type w} →       [inst : Semiring 
𝕜] →         [inst_1 : AddCommMonoid E] →           [inst_2 : _root_.Module 𝕜 E]
 →             [inst_3 : TopologicalSpace E] →               [inst_4 : Continuou
sAdd E] →                 [inst_5 : ContinuousConstSMul 𝕜 E] →                  
 [inst_6 : AddCommMonoid F] →                     [inst_7 : _root_.Module 𝕜 F] →
                       [inst_8 : TopologicalSpace F] →                         [
inst_9 : ContinuousAdd F] →                           [inst_10 : ContinuousConst
SMul 𝕜 F] →                             FormalMultilinearSeries 𝕜 E F → FormalMu
ltilinearSeries 𝕜 E F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Killing the zeroth coefficient in a formal multilinear series
-/
def removeZero (p : FormalMultilinearSeries 𝕜 E F) : FormalMultilinearSeries 𝕜 E F
  | 0 => 0
  | n + 1 => p (n + 1)

@[simp]
/-
**FormalMultilinearSeries.removeZero_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `Forma
lMultilinearSeries`。
形式化陈述：removeZero_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) : p.removeZero 0
 = 0
参数：p : FormalMultilinearSeries 𝕜 E F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem removeZero_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) : p.removeZero 0 = 0 :=
  rfl

@[simp]
/-
**FormalMultilinearSeries.removeZero_coeff_succ** 是 Mathlib 中的一个定理，位于命名空间 `Forma
lMultilinearSeries`。
形式化陈述：removeZero_coeff_succ (p : FormalMultilinearSeries 𝕜 E F) (n : Nat) : p.re
moveZero (n + 1) = p (n + 1)
参数：p : FormalMultilinearSeries 𝕜 E F；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem removeZero_coeff_succ (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) :
    p.removeZero (n + 1) = p (n + 1) :=
  rfl
/-
**FormalMultilinearSeries.removeZero_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `FormalMul
tilinearSeries`。
形式化陈述：removeZero_of_pos (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (h : 0 < n
) : p.removeZero n = p n
参数：p : FormalMultilinearSeries 𝕜 E F；h : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
-/
theorem removeZero_of_pos (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (h : 0 < n) :
    p.removeZero n = p n := by
  rw [← Nat.succ_pred_eq_of_pos h]
  rfl

/-- Convenience congruence lemma stating in a dependent setting that, if the arguments to a formal
multilinear series are equal, then the values are also equal. -/
/-
**FormalMultilinearSeries.congr** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinearSeri
es`。
形式化陈述：congr (p : FormalMultilinearSeries 𝕜 E F) {m n : Nat} {v : Fin m -> E} {w 
: Fin n -> E} (h1 : m = n) (h2 : forall (i : Nat) (him : i < m) (hin : i < n), v
 ⟨i, him⟩ = w ⟨i, hin⟩) : p m v = p n w
参数：p : FormalMultilinearSeries 𝕜 E F；h1 : m = n；h2 : forall (i : Nat) (him : i <
 m) (hin : i < n), v ⟨i, him⟩ = w ⟨i, hin⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Convenience congruence lemma stating in a dependent setting that, if the argumen
ts to a formal
multilinear series are equal, then the values are also equal.
-/
theorem congr (p : FormalMultilinearSeries 𝕜 E F) {m n : ℕ} {v : Fin m → E} {w : Fin n → E}
    (h1 : m = n) (h2 : ∀ (i : ℕ) (him : i < m) (hin : i < n), v ⟨i, him⟩ = w ⟨i, hin⟩) :
    p m v = p n w := by
  subst n
  congr with ⟨i, hi⟩
  exact h2 i hi hi
/-
**FormalMultilinearSeries.congr_zero** 是 Mathlib 中的一个引理，位于命名空间 `FormalMultilinea
rSeries`。
形式化陈述：congr_zero (p : FormalMultilinearSeries 𝕜 E F) {k l : Nat} (h : k = l) (h'
 : p k = 0) : p l = 0
参数：p : FormalMultilinearSeries 𝕜 E F；h : k = l；h' : p k = 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma congr_zero (p : FormalMultilinearSeries 𝕜 E F) {k l : ℕ} (h : k = l) (h' : p k = 0) :
    p l = 0 := by
  subst h; exact h'

/-- Composing each term `pₙ` in a formal multilinear series with `(u, ..., u)` where `u` is a fixed
continuous linear map, gives a new formal multilinear series `p.compContinuousLinearMap u`. -/
/-
**FormalMultilinearSeries.compContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `For
malMultilinearSeries`。
形式化陈述：compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] 
F) : FormalMultilinearSeries 𝕜 E G
参数：p : FormalMultilinearSeries 𝕜 F G；u : E ->L[𝕜] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing each term `pₙ` in a formal multilinear series with `(u, ..., u)` where
 `u` is a fixed
continuous linear map, gives a new formal multilinear series `p.compContinuousLi
nearMap u`.
-/
def compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) :
    FormalMultilinearSeries 𝕜 E G := fun n => (p n).compContinuousLinearMap fun _ : Fin n => u

@[simp]
/-
**FormalMultilinearSeries.compContinuousLinearMap_apply** 是 Mathlib 中的一个定理，位于命名空
间 `FormalMultilinearSeries`。
形式化陈述：compContinuousLinearMap_apply (p : FormalMultilinearSeries 𝕜 F G) (u : E -
>L[𝕜] F) (n : Nat) (v : Fin n -> E) : (p.compContinuousLinearMap u) n v = p n (u
 ∘ v)
参数：p : FormalMultilinearSeries 𝕜 F G；u : E ->L[𝕜] F；n : Nat；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compContinuousLinearMap_apply (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) (n : ℕ)
    (v : Fin n → E) : (p.compContinuousLinearMap u) n v = p n (u ∘ v) :=
  rfl

@[simp]
/-
**FormalMultilinearSeries.compContinuousLinearMap_id** 是 Mathlib 中的一个定理，位于命名空间 `
FormalMultilinearSeries`。
形式化陈述：compContinuousLinearMap_id (p : FormalMultilinearSeries 𝕜 E F) : p.compCon
tinuousLinearMap (.id _ _) = p
参数：p : FormalMultilinearSeries 𝕜 E F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compContinuousLinearMap_id (p : FormalMultilinearSeries 𝕜 E F) :
    p.compContinuousLinearMap (.id _ _) = p :=
  rfl
/-
**FormalMultilinearSeries.compContinuousLinearMap_comp** 是 Mathlib 中的一个定理，位于命名空间
 `FormalMultilinearSeries`。
形式化陈述：compContinuousLinearMap_comp (p : FormalMultilinearSeries 𝕜 G H) (u₁ : F -
>L[𝕜] G) (u₂ : E ->L[𝕜] F) : (p.compContinuousLinearMap u₁).compContinuousLinear
Map u₂ = p.compContinuousLinearMap (u₁.comp u₂)
参数：p : FormalMultilinearSeries 𝕜 G H；u₁ : F ->L[𝕜] G；u₂ : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compContinuousLinearMap_comp (p : FormalMultilinearSeries 𝕜 G H) (u₁ : F →L[𝕜] G)
    (u₂ : E →L[𝕜] F) :
    (p.compContinuousLinearMap u₁).compContinuousLinearMap u₂ =
    p.compContinuousLinearMap (u₁.comp u₂) :=
  rfl

variable (𝕜) [Semiring 𝕜'] [SMul 𝕜 𝕜']
variable [Module 𝕜' E] [ContinuousConstSMul 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
variable [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [IsScalarTower 𝕜 𝕜' F]

/-- Reinterpret a formal `𝕜'`-multilinear series as a formal `𝕜`-multilinear series. -/
@[simp]
/-
**FormalMultilinearSeries.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `FormalMulti
linearSeries`。
形式化陈述：(𝕜 : Type u) →   {𝕜' : Type u'} →     {E : Type v} →       {F : Type w} → 
        [inst : Semiring 𝕜] →           [inst_1 : AddCommMonoid E] →            
 [inst_2 : _root_.Module 𝕜 E] →               [inst_3 : TopologicalSpace E] →   
              [inst_4 : ContinuousAdd E] →                   [inst_5 : Continuou
sConstSMul 𝕜 E] →                     [inst_6 : AddCommMonoid F] →              
         [inst_7 : _root_.Module 𝕜 F] →                         [inst_8 : Topolo
gicalSpace F] →                           [inst_9 : ContinuousAdd F] →          
                   [inst_10 : ContinuousConstSMul 𝕜 F] →                        
       [inst_11 : Semiring 𝕜'] →                                 [inst_12 : SMul
 𝕜 𝕜'] →                                   [inst_13 : _root_.Module 𝕜' E] →     
                                [inst_14 : ContinuousConstSMul 𝕜' E] →          
                             [IsScalarTower 𝕜 𝕜' E] →                           
              [inst_16 : _root_.Module 𝕜' F] →                                  
         [inst_17 : ContinuousConstSMul 𝕜' F] →                                 
            [IsScalarTower 𝕜 𝕜' F] →                                            
   FormalMultilinearSeries 𝕜' E F → FormalMultilinearSeries 𝕜 E F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a formal `𝕜'`-multilinear series as a formal `𝕜`-multilinear series.
-/
protected def restrictScalars (p : FormalMultilinearSeries 𝕜' E F) :
    FormalMultilinearSeries 𝕜 E F := fun n => (p n).restrictScalars 𝕜

end FormalMultilinearSeries

end

namespace FormalMultilinearSeries
variable [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousConstSMul 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]

/-
**FormalMultilinearSeries.** 是 Mathlib 中的一个实例，位于命名空间 `FormalMultilinearSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (FormalMultilinearSeries 𝕜 E F) :=
  inferInstanceAs <| AddCommGroup <| ∀ n : ℕ, E [×n]→L[𝕜] F

@[simp]
/-
**FormalMultilinearSeries.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinear
Series`。
形式化陈述：neg_apply (f : FormalMultilinearSeries 𝕜 E F) (n : Nat) : (-f) n = - f n
参数：f : FormalMultilinearSeries 𝕜 E F；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem neg_apply (f : FormalMultilinearSeries 𝕜 E F) (n : ℕ) : (-f) n = - f n := rfl

@[simp]
/-
**FormalMultilinearSeries.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinear
Series`。
形式化陈述：sub_apply (f g : FormalMultilinearSeries 𝕜 E F) (n : Nat) : (f - g) n = f 
n - g n
参数：f g : FormalMultilinearSeries 𝕜 E F；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem sub_apply (f g : FormalMultilinearSeries 𝕜 E F) (n : ℕ) : (f - g) n = f n - g n := rfl

end FormalMultilinearSeries

namespace FormalMultilinearSeries

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]

variable (p : FormalMultilinearSeries 𝕜 E F)

/-- Forgetting the zeroth term in a formal multilinear series, and interpreting the following terms
as multilinear maps into `E →L[𝕜] F`. If `p` is the Taylor series (`HasFTaylorSeriesUpTo`) of a
function, then `p.shift` is the Taylor series of the derivative of the function. Note that the
`p.sum` of a Taylor series `p` does not give the original function; for a formal multilinear
series that sums to the derivative of `p.sum`, see `HasFPowerSeriesOnBall.fderiv`. -/
/-
**FormalMultilinearSeries.shift** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilinearSeri
es`。
形式化陈述：shift : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Forgetting the zeroth term in a formal multilinear series, and interpreting the 
following terms
as multilinear maps into `E →L[𝕜] F`. If `p` is the Taylor series (`HasFTaylorSe
riesUpTo`) of a
function, then `p.shift` is the Taylor series of the derivative of the function.
 Note that the
`p.sum` of a Taylor series `p` does not give the original function; for a formal
 multilinear
series that sums to the derivative of `p.sum`, see `HasFPowerSeriesOnBall.fderiv
`.
-/
def shift : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F) := fun n => (p n.succ).curryRight

/-- Adding a zeroth term to a formal multilinear series taking values in `E →L[𝕜] F`. This
corresponds to starting from a Taylor series (`HasFTaylorSeriesUpTo`) for the derivative of a
function, and building a Taylor series for the function itself. -/
/-
**FormalMultilinearSeries.unshift** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilinearSe
ries`。
形式化陈述：{𝕜 : Type u} →   {E : Type v} →     {F : Type w} →       [inst : Nontrivia
llyNormedField 𝕜] →         [inst_1 : NormedAddCommGroup E] →           [inst_2 
: NormedSpace 𝕜 E] →             [inst_3 : NormedAddCommGroup F] →              
 [inst_4 : NormedSpace 𝕜 F] → FormalMultilinearSeries 𝕜 E (E →L[𝕜] F) → F → Form
alMultilinearSeries 𝕜 E F
参数：E →L[𝕜] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adding a zeroth term to a formal multilinear series taking values in `E →L[𝕜] F`
. This
corresponds to starting from a Taylor series (`HasFTaylorSeriesUpTo`) for the de
rivative of a
function, and building a Taylor series for the function itself.
-/
def unshift (q : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)) (z : F) : FormalMultilinearSeries 𝕜 E F
  | 0 => (continuousMultilinearCurryFin0 𝕜 E F).symm z
  | n + 1 => (continuousMultilinearCurryRightEquiv' 𝕜 n E F).symm (q n)
/-
**FormalMultilinearSeries.unshift_shift** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultili
nearSeries`。
形式化陈述：unshift_shift {p : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)} {z : F} : (p.
unshift z).shift = p
参数：E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
-/
theorem unshift_shift {p : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)} {z : F} :
    (p.unshift z).shift = p := by
  ext1 n
  simp only [shift, Nat.succ_eq_add_one, unshift]
  exact LinearIsometryEquiv.apply_symm_apply (continuousMultilinearCurryRightEquiv' 𝕜 n E F) (p n)

end FormalMultilinearSeries

section

variable [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousConstSMul 𝕜 E] [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousAdd F] [ContinuousConstSMul 𝕜 F] [AddCommMonoid G] [Module 𝕜 G]
  [TopologicalSpace G] [ContinuousAdd G] [ContinuousConstSMul 𝕜 G]

namespace ContinuousLinearMap

/-- Composing each term `pₙ` in a formal multilinear series with a continuous linear map `f` on the
left gives a new formal multilinear series `f.compFormalMultilinearSeries p` whose general term
is `f ∘ pₙ`. -/
/-
**ContinuousLinearMap.compFormalMultilinearSeries** 是 Mathlib 中的一个定义，位于命名空间 `Con
tinuousLinearMap`。
形式化陈述：compFormalMultilinearSeries (f : F ->L[𝕜] G) (p : FormalMultilinearSeries 
𝕜 E F) : FormalMultilinearSeries 𝕜 E G
参数：f : F ->L[𝕜] G；p : FormalMultilinearSeries 𝕜 E F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing each term `pₙ` in a formal multilinear series with a continuous linear
 map `f` on the
left gives a new formal multilinear series `f.compFormalMultilinearSeries p` who
se general term
is `f ∘ pₙ`.
-/
def compFormalMultilinearSeries (f : F →L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 E G := fun n => f.compContinuousMultilinearMap (p n)

@[simp]
/-
**ContinuousLinearMap.compFormalMultilinearSeries_apply** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousLinearMap`。
形式化陈述：compFormalMultilinearSeries_apply (f : F ->L[𝕜] G) (p : FormalMultilinearS
eries 𝕜 E F) (n : Nat) : (f.compFormalMultilinearSeries p) n = f.compContinuousM
ultilinearMap (p n)
参数：f : F ->L[𝕜] G；p : FormalMultilinearSeries 𝕜 E F；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compFormalMultilinearSeries_apply (f : F →L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F)
    (n : ℕ) : (f.compFormalMultilinearSeries p) n = f.compContinuousMultilinearMap (p n) :=
  rfl
/-
**ContinuousLinearMap.compFormalMultilinearSeries_apply'** 是 Mathlib 中的一个定理，位于命名
空间 `ContinuousLinearMap`。
形式化陈述：compFormalMultilinearSeries_apply' (f : F ->L[𝕜] G) (p : FormalMultilinear
Series 𝕜 E F) (n : Nat) (v : Fin n -> E) : (f.compFormalMultilinearSeries p) n v
 = f (p n v)
参数：f : F ->L[𝕜] G；p : FormalMultilinearSeries 𝕜 E F；n : Nat；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compFormalMultilinearSeries_apply' (f : F →L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F)
    (n : ℕ) (v : Fin n → E) : (f.compFormalMultilinearSeries p) n v = f (p n v) :=
  rfl

end ContinuousLinearMap

namespace ContinuousMultilinearMap

variable {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [∀ i, TopologicalSpace (E i)] [∀ i, IsTopologicalAddGroup (E i)]
  [∀ i, ContinuousConstSMul 𝕜 (E i)] [Fintype ι] (f : ContinuousMultilinearMap 𝕜 E F)

/-- Realize a ContinuousMultilinearMap on `∀ i : ι, E i` as the evaluation of a
FormalMultilinearSeries by choosing an arbitrary identification `ι ≃ Fin (Fintype.card ι)`. -/
/-
**ContinuousMultilinearMap.toFormalMultilinearSeries** 是 Mathlib 中的一个定义，位于命名空间 `
ContinuousMultilinearMap`。
形式化陈述：toFormalMultilinearSeries : FormalMultilinearSeries 𝕜 (forall i, E i) F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Realize a ContinuousMultilinearMap on `∀ i : ι, E i` as the evaluation of a
FormalMultilinearSeries by choosing an arbitrary identification `ι ≃ Fin (Fintyp
e.card ι)`.
-/
noncomputable def toFormalMultilinearSeries : FormalMultilinearSeries 𝕜 (∀ i, E i) F :=
  fun n ↦ if h : Fintype.card ι = n then
    (f.compContinuousLinearMap .proj).domDomCongr (Fintype.equivFinOfCardEq h)
  else 0

end ContinuousMultilinearMap

end

namespace FormalMultilinearSeries

section Order

variable [Semiring 𝕜] {n : ℕ} [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousConstSMul 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
  [TopologicalSpace F] [ContinuousAdd F] [ContinuousConstSMul 𝕜 F]
  {p : FormalMultilinearSeries 𝕜 E F}

/-- The index of the first non-zero coefficient in `p` (or `0` if all coefficients are zero). This
  is the order of the isolated zero of an analytic function `f` at a point if `p` is the Taylor
  series of `f` at that point. -/
/-
**FormalMultilinearSeries.order** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilinearSeri
es`。
形式化陈述：order (p : FormalMultilinearSeries 𝕜 E F) : Nat
参数：p : FormalMultilinearSeries 𝕜 E F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The index of the first non-zero coefficient in `p` (or `0` if all coefficients a
re zero). This
  is the order of the isolated zero of an analytic function `f` at a point if `p
` is the Taylor
  series of `f` at that point.
-/
noncomputable def order (p : FormalMultilinearSeries 𝕜 E F) : ℕ :=
  sInf { n | p n ≠ 0 }

@[simp]
/-
**FormalMultilinearSeries.order_zero** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinea
rSeries`。
形式化陈述：order_zero : (0 : FormalMultilinearSeries 𝕜 E F).order = 0
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Nat.sInf_empty`：sInf_empty : sInf ∅ = 0
-/
theorem order_zero : (0 : FormalMultilinearSeries 𝕜 E F).order = 0 := by simp [order]
/-
**FormalMultilinearSeries.ne_zero_of_order_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fo
rmalMultilinearSeries`。
形式化陈述：ne_zero_of_order_ne_zero (hp : p.order != 0) : p != 0
参数：hp : p.order != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.order_zero`：order_zero : (0 : FormalMultilinearS
eries 𝕜 E F).order = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem ne_zero_of_order_ne_zero (hp : p.order ≠ 0) : p ≠ 0 := fun h => by simp [h] at hp

set_option backward.isDefEq.respectTransparency false in
/-
**FormalMultilinearSeries.order_eq_find** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultili
nearSeries`。
形式化陈述：order_eq_find [DecidablePred fun n => p n != 0] (hp : exists n, p n != 0) 
: p.order = Nat.find hp
参数：hp : exists n, p n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.sInf_def`：sInf_def {s : Set Nat} (h : s.Nonempty) : sInf s = @Nat.fi
nd (fun n => n in s) _ h
-/
theorem order_eq_find [DecidablePred fun n => p n ≠ 0] (hp : ∃ n, p n ≠ 0) :
    p.order = Nat.find hp := by convert! Nat.sInf_def hp
/-
**FormalMultilinearSeries.order_eq_find'** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultil
inearSeries`。
形式化陈述：order_eq_find' [DecidablePred fun n => p n != 0] (hp : p != 0) : p.order =
 Nat.find (FormalMultilinearSeries.ne_iff.mp hp)
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FormalMultilinearSeries.order_eq_find`：order_eq_find [DecidablePred fun 
n => p n != 0] (hp : exists n, p n != 0) : p.order = Nat.find hp
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FormalMultilinearSeries.ne_iff`：∀ {𝕜 : Type u} {E : Type v} {F : Type w}
 [inst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [
inst_3 : Topological…
-/
theorem order_eq_find' [DecidablePred fun n => p n ≠ 0] (hp : p ≠ 0) :
    p.order = Nat.find (FormalMultilinearSeries.ne_iff.mp hp) :=
  order_eq_find _
/-
**FormalMultilinearSeries.order_eq_zero_iff'** 是 Mathlib 中的一个定理，位于命名空间 `FormalMu
ltilinearSeries`。
形式化陈述：order_eq_zero_iff' : p.order = 0 ↔ p = 0 ∨ p 0 != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
-/
theorem order_eq_zero_iff' : p.order = 0 ↔ p = 0 ∨ p 0 ≠ 0 := by
  simpa [order, Nat.sInf_eq_zero, FormalMultilinearSeries.ext_iff, eq_empty_iff_forall_notMem]
    using or_comm
/-
**FormalMultilinearSeries.order_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `FormalMul
tilinearSeries`。
形式化陈述：order_eq_zero_iff (hp : p != 0) : p.order = 0 ↔ p 0 != 0
参数：hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem order_eq_zero_iff (hp : p ≠ 0) : p.order = 0 ↔ p 0 ≠ 0 := by
  simp [order_eq_zero_iff', hp]
/-
**FormalMultilinearSeries.apply_order_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `FormalM
ultilinearSeries`。
形式化陈述：apply_order_ne_zero (hp : p != 0) : p p.order != 0
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sInf_mem`：sInf_mem {s : Set Nat} (h : s.Nonempty) : sInf s in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FormalMultilinearSeries.ne_iff`：∀ {𝕜 : Type u} {E : Type v} {F : Type w}
 [inst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [
inst_3 : Topological…
-/
theorem apply_order_ne_zero (hp : p ≠ 0) : p p.order ≠ 0 :=
  Nat.sInf_mem (FormalMultilinearSeries.ne_iff.1 hp)
/-
**FormalMultilinearSeries.apply_order_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Formal
MultilinearSeries`。
形式化陈述：apply_order_ne_zero' (hp : p.order != 0) : p p.order != 0
参数：hp : p.order != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FormalMultilinearSeries.apply_order_ne_zero`：apply_order_ne_zero (hp : p
 != 0) : p p.order != 0
· 使用定理 `FormalMultilinearSeries.ne_zero_of_order_ne_zero`：ne_zero_of_order_ne_ze
ro (hp : p.order != 0) : p != 0
-/
theorem apply_order_ne_zero' (hp : p.order ≠ 0) : p p.order ≠ 0 :=
  apply_order_ne_zero (ne_zero_of_order_ne_zero hp)
/-
**FormalMultilinearSeries.apply_eq_zero_of_lt_order** 是 Mathlib 中的一个定理，位于命名空间 `F
ormalMultilinearSeries`。
形式化陈述：apply_eq_zero_of_lt_order (hp : n < p.order) : p n = 0
参数：hp : n < p.order。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Nat.notMem_of_lt_sInf`：notMem_of_lt_sInf {s : Set Nat} {m : Nat} (hm : m
 < sInf s) : m ∉ s
-/
theorem apply_eq_zero_of_lt_order (hp : n < p.order) : p n = 0 :=
  by_contra <| Nat.notMem_of_lt_sInf hp

end Order

section Coef

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 → E} {n : ℕ} {z : 𝕜} {y : Fin n → 𝕜}

/-- The `n`th coefficient of `p` when seen as a power series. -/
/-
**FormalMultilinearSeries.coeff** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilinearSeri
es`。
形式化陈述：coeff (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : Nat) : E
参数：p : FormalMultilinearSeries 𝕜 𝕜 E；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th coefficient of `p` when seen as a power series.
-/
def coeff (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) : E :=
  p n 1
/-
**FormalMultilinearSeries.mkPiRing_coeff_eq** 是 Mathlib 中的一个定理，位于命名空间 `FormalMul
tilinearSeries`。
形式化陈述：mkPiRing_coeff_eq (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : Nat) : Continuo
usMultilinearMap.mkPiRing 𝕜 (Fin n) (p.coeff n) = p n
参数：p : FormalMultilinearSeries 𝕜 𝕜 E；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.mkPiRing_apply_one_eq_self`：mkPiRing_apply_one_
eq_self (f : ContinuousMultilinearMap R (fun _ : ι => R) M) : ContinuousMultilin
earMap.mkPiRing R ι (f fun _ => 1) = f
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem mkPiRing_coeff_eq (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) :
    ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (p.coeff n) = p n :=
  (p n).mkPiRing_apply_one_eq_self

@[simp]
/-
**FormalMultilinearSeries.apply_eq_prod_smul_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Fo
rmalMultilinearSeries`。
形式化陈述：apply_eq_prod_smul_coeff : p n y = (∏ i, y i) • p.coeff n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MultilinearMap.map_smul_univ`：map_smul_univ [Fintype ι] (c : ι -> R) (m 
: forall i, M₁ i) : (f fun i => c i • m i) = (∏ i, c i) • f m
-/
theorem apply_eq_prod_smul_coeff : p n y = (∏ i, y i) • p.coeff n := by
  convert! (p n).toMultilinearMap.map_smul_univ y 1
  simp only [Pi.one_apply, smul_eq_mul, mul_one]
/-
**FormalMultilinearSeries.coeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultili
nearSeries`。
形式化陈述：coeff_eq_zero : p.coeff n = 0 ↔ p n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FormalMultilinearSeries.mkPiRing_coeff_eq`：mkPiRing_coeff_eq (p : Formal
MultilinearSeries 𝕜 𝕜 E) (n : Nat) : ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n)
 (p.coeff n) = p n
· 使用定理 `ContinuousMultilinearMap.mkPiRing_eq_zero_iff`：mkPiRing_eq_zero_iff (z :
 M) : ContinuousMultilinearMap.mkPiRing R ι z = 0 ↔ z = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coeff_eq_zero : p.coeff n = 0 ↔ p n = 0 := by
  rw [← mkPiRing_coeff_eq p, ContinuousMultilinearMap.mkPiRing_eq_zero_iff]
/-
**FormalMultilinearSeries.apply_eq_pow_smul_coeff** 是 Mathlib 中的一个定理，位于命名空间 `For
malMultilinearSeries`。
形式化陈述：apply_eq_pow_smul_coeff : (p n fun _ => z) = z ^ n • p.coeff n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.apply_eq_prod_smul_coeff`：apply_eq_prod_smul_coe
ff : p n y = (∏ i, y i) • p.coeff n
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem apply_eq_pow_smul_coeff : (p n fun _ => z) = z ^ n • p.coeff n := by simp

@[simp]
/-
**FormalMultilinearSeries.norm_apply_eq_norm_coef** 是 Mathlib 中的一个定理，位于命名空间 `For
malMultilinearSeries`。
形式化陈述：norm_apply_eq_norm_coef : ‖p n‖ = ‖coeff p n‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FormalMultilinearSeries.mkPiRing_coeff_eq`：mkPiRing_coeff_eq (p : Formal
MultilinearSeries 𝕜 𝕜 E) (n : Nat) : ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n)
 (p.coeff n) = p n
· 使用定理 `ContinuousMultilinearMap.norm_mkPiRing`：norm_mkPiRing (z : G) : ‖Continu
ousMultilinearMap.mkPiRing 𝕜 ι z‖ = ‖z‖
-/
theorem norm_apply_eq_norm_coef : ‖p n‖ = ‖coeff p n‖ := by
  rw [← mkPiRing_coeff_eq p, ContinuousMultilinearMap.norm_mkPiRing]

end Coef

section Fslope

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : FormalMultilinearSeries 𝕜 𝕜 E} {n : ℕ}

/-- The formal counterpart of `dslope`, corresponding to the expansion of `(f z - f 0) / z`. If `f`
has `p` as a power series, then `dslope f` has `fslope p` as a power series. -/
/-
**FormalMultilinearSeries.fslope** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilinearSer
ies`。
形式化陈述：fslope (p : FormalMultilinearSeries 𝕜 𝕜 E) : FormalMultilinearSeries 𝕜 𝕜 E
参数：p : FormalMultilinearSeries 𝕜 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The formal counterpart of `dslope`, corresponding to the expansion of `(f z - f 
0) / z`. If `f`
has `p` as a power series, then `dslope f` has `fslope p` as a power series.
-/
noncomputable def fslope (p : FormalMultilinearSeries 𝕜 𝕜 E) : FormalMultilinearSeries 𝕜 𝕜 E :=
  fun n => (p (n + 1)).curryLeft 1

@[simp]
/-
**FormalMultilinearSeries.coeff_fslope** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilin
earSeries`。
形式化陈述：coeff_fslope : p.fslope.coeff n = p.coeff (n + 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Fin.cons_self_tail`：cons_self_tail : cons (q 0) (tail q) = q
-/
theorem coeff_fslope : p.fslope.coeff n = p.coeff (n + 1) := by
  simp only [fslope, coeff, ContinuousMultilinearMap.curryLeft_apply]
  congr 1
  exact Fin.cons_self_tail (fun _ => (1 : 𝕜))

@[simp]
/-
**FormalMultilinearSeries.coeff_iterate_fslope** 是 Mathlib 中的一个定理，位于命名空间 `Formal
MultilinearSeries`。
形式化陈述：coeff_iterate_fslope (k n : Nat) : (fslope^[k] p).coeff n = p.coeff (n + k
)
参数：k n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.coeff_fslope`：coeff_fslope : p.fslope.coeff n = 
p.coeff (n + 1)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_iterate_fslope (k n : ℕ) : (fslope^[k] p).coeff n = p.coeff (n + k) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih => simp [ih, add_assoc]

end Fslope

end FormalMultilinearSeries

section Const

/-- The formal multilinear series where all terms of positive degree are equal to zero, and the term
of degree zero is `c`. It is the power series expansion of the constant function equal to `c`
everywhere. -/
/-
**constFormalMultilinearSeries** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_1) →   [inst : NontriviallyNormedField 𝕜] →     (E : Type u_2)
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          [inst_3 : ContinuousConstSMul 𝕜 E] →             [inst_4 : IsTopologic
alAddGroup E] →               {F : Type u_3} →                 [inst_5 : NormedA
ddCommGroup F] →                   [inst_6 : IsTopologicalAddGroup F] →         
            [inst_7 : NormedSpace 𝕜 F] → [inst_8 : ContinuousConstSMul 𝕜 F] → F 
→ FormalMultilinearSeries 𝕜 E F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The formal multilinear series where all terms of positive degree are equal to ze
ro, and the term
of degree zero is `c`. It is the power series expansion of the constant function
 equal to `c`
everywhere.
-/
def constFormalMultilinearSeries (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ContinuousConstSMul 𝕜 E] [IsTopologicalAddGroup E]
    {F : Type*} [NormedAddCommGroup F] [IsTopologicalAddGroup F] [NormedSpace 𝕜 F]
    [ContinuousConstSMul 𝕜 F] (c : F) : FormalMultilinearSeries 𝕜 E F
  | 0 => ContinuousMultilinearMap.uncurry0 _ _ c
  | _ => 0

@[simp]
/-
**constFormalMultilinearSeries_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：constFormalMultilinearSeries_apply_zero [NontriviallyNormedField 𝕜] [Norme
dAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {c :
 F} : constFormalMultilinearSeries 𝕜 E c 0 = ContinuousMultilinearMap.uncurry0 _
 _ c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem constFormalMultilinearSeries_apply_zero [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {c : F} :
    constFormalMultilinearSeries 𝕜 E c 0 = ContinuousMultilinearMap.uncurry0 _ _ c :=
  rfl

@[simp]
/-
**constFormalMultilinearSeries_apply_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：constFormalMultilinearSeries_apply_succ [NontriviallyNormedField 𝕜] [Norme
dAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {c :
 F} {n : Nat} : constFormalMultilinearSeries 𝕜 E c (n + 1) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem constFormalMultilinearSeries_apply_succ [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {c : F} {n : ℕ} :
    constFormalMultilinearSeries 𝕜 E c (n + 1) = 0 :=
  rfl
/-
**constFormalMultilinearSeries_apply_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：constFormalMultilinearSeries_apply_of_nonzero [NontriviallyNormedField 𝕜] 
[NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F
] {c : F} {n : Nat} (hn : n != 0) : constFormalMultilinearSeries 𝕜 E c n = 0
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem constFormalMultilinearSeries_apply_of_nonzero [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {c : F}
    {n : ℕ} (hn : n ≠ 0) : constFormalMultilinearSeries 𝕜 E c n = 0 :=
  Nat.casesOn n (fun hn => (hn rfl).elim) (fun _ _ => rfl) hn

@[simp]
/-
**constFormalMultilinearSeries_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：constFormalMultilinearSeries_zero [NontriviallyNormedField 𝕜] [NormedAddCo
mmGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] : constFor
malMultilinearSeries 𝕜 E (0 : F) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma constFormalMultilinearSeries_zero [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] :
    constFormalMultilinearSeries 𝕜 E (0 : F) = 0 := by
  ext n
  induction n <;> simp

@[simp]
/-
**compContinuousLinearMap_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：compContinuousLinearMap_zero [NontriviallyNormedField 𝕜] [NormedAddCommGro
up E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommG
roup G] [NormedSpace 𝕜 G] (p : FormalMultilinearSeries 𝕜 F G) : p.compContinuous
LinearMap (0 : E ->L[𝕜] F) = constFormalMultilinearSeries 𝕜 E (p 0 0)
参数：p : FormalMultilinearSeries 𝕜 F G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `constFormalMultilinearSeries.congr_simp`：∀ (𝕜 : Type u_1) [inst : Nontri
viallyNormedField 𝕜] (E : Type u_2) [inst_1 : NormedAddCommGroup E]   [inst_2 : 
NormedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `ContinuousMultilinearMap.map_zero`：map_zero [Nonempty ι] : f 0 = 0
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma compContinuousLinearMap_zero [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (p : FormalMultilinearSeries 𝕜 F G) :
    p.compContinuousLinearMap (0 : E →L[𝕜] F) = constFormalMultilinearSeries 𝕜 E (p 0 0) := by
  ext n v
  cases n with
  | zero =>
    simp only [FormalMultilinearSeries.compContinuousLinearMap_apply, Matrix.zero_empty,
      constFormalMultilinearSeries_apply_zero, ContinuousMultilinearMap.uncurry0_apply]
    congr
    apply Subsingleton.allEq
  | succ =>
    simp [FunLike.coe_zero]

end Const

section Linear

variable [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace ContinuousLinearMap

/-- Formal power series of a continuous linear map `f : E →L[𝕜] F` at `x : E`:
`f y = f x + f (y - x)`. -/
/-
**ContinuousLinearMap.fpowerSeries** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：{𝕜 : Type u} →   {E : Type v} →     {F : Type w} →       [inst : Nontrivia
llyNormedField 𝕜] →         [inst_1 : NormedAddCommGroup E] →           [inst_2 
: NormedSpace 𝕜 E] →             [inst_3 : NormedAddCommGroup F] →              
 [inst_4 : NormedSpace 𝕜 F] → (E →L[𝕜] F) → E → FormalMultilinearSeries 𝕜 E F
参数：E →L[𝕜] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Formal power series of a continuous linear map `f : E →L[𝕜] F` at `x : E`:
`f y = f x + f (y - x)`.
-/
def fpowerSeries (f : E →L[𝕜] F) (x : E) : FormalMultilinearSeries 𝕜 E F
  | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ (f x)
  | 1 => (continuousMultilinearCurryFin1 𝕜 E F).symm f
  | _ => 0

@[simp]
/-
**ContinuousLinearMap.fpowerSeries_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：fpowerSeries_apply_zero (f : E ->L[𝕜] F) (x : E) : f.fpowerSeries x 0 = Co
ntinuousMultilinearMap.uncurry0 𝕜 _ (f x)
参数：f : E ->L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fpowerSeries_apply_zero (f : E →L[𝕜] F) (x : E) :
    f.fpowerSeries x 0 = ContinuousMultilinearMap.uncurry0 𝕜 _ (f x) :=
  rfl

@[simp]
/-
**ContinuousLinearMap.fpowerSeries_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：fpowerSeries_apply_one (f : E ->L[𝕜] F) (x : E) : f.fpowerSeries x 1 = (co
ntinuousMultilinearCurryFin1 𝕜 E F).symm f
参数：f : E ->L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fpowerSeries_apply_one (f : E →L[𝕜] F) (x : E) :
    f.fpowerSeries x 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm f :=
  rfl

@[simp]
/-
**ContinuousLinearMap.fpowerSeries_apply_add_two** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousLinearMap`。
形式化陈述：fpowerSeries_apply_add_two (f : E ->L[𝕜] F) (x : E) (n : Nat) : f.fpowerSe
ries x (n + 2) = 0
参数：f : E ->L[𝕜] F；x : E；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fpowerSeries_apply_add_two (f : E →L[𝕜] F) (x : E) (n : ℕ) : f.fpowerSeries x (n + 2) = 0 :=
  rfl

end ContinuousLinearMap

end Linear

