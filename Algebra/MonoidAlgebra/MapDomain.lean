/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Maps of monoid algebras

This file defines maps of monoid algebras along both the ring and monoid arguments.
-/

assert_not_exists NonUnitalAlgHom AlgEquiv

@[expose] public noncomputable section

open Function
open Finsupp hiding single mapDomain

variable {ι F R S T M N O : Type*}

namespace MonoidAlgebra
section Semiring
variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

/-- Given a function `f : M → N` between magmas, return the corresponding map `R[M] → R[N]` obtained
by summing the coefficients along each fiber of `f`. -/
@[to_additive (attr := simps)
/-- Given a function `f : M → N` between magmas, return the corresponding map `R[M] → R[N]` obtained
by summing the coefficients along each fiber of `f`. -/]
/-
**MonoidAlgebra.mapDomain** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomain (f : M -> N) (x : R[M]) : R[N]
参数：f : M -> N；x : R[M]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapDomain (f : M → N) (x : R[M]) : R[N] := .ofCoeff <| Finsupp.mapDomain f x.coeff

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapDomain_zero** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomain_zero (f : M -> N) : mapDomain f (0 : R[M]) = 0
参数：f : M -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.coeff_mapDomain`：∀ {R : Type u_3} {M : Type u_6} {N : Type
 u_7} [inst : Semiring R] (f : M → N) (x : MonoidAlgebra R M),   (MonoidAlgebra.
mapDomain f x).coef…
· 使用定理 `Finsupp.mapDomain_zero`：mapDomain_zero {f : α -> β} : mapDomain f (0 : α
 ->₀ M) = (0 : β ->₀ M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomain_zero (f : M → N) : mapDomain f (0 : R[M]) = 0 := by ext; simp

@[to_additive]
/-
**MonoidAlgebra.mapDomain_add** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomain_add (f : M -> N) (x y : R[M]) : mapDomain f (x + y) = mapDomain 
f x + mapDomain f y
参数：f : M -> N；x y : R[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidAlgebra.coeff_mapDomain`：∀ {R : Type u_3} {M : Type u_6} {N : Type
 u_7} [inst : Semiring R] (f : M → N) (x : MonoidAlgebra R M),   (MonoidAlgebra.
mapDomain f x).coef…
· 使用定理 `Finsupp.mapDomain_add`：mapDomain_add {f : α -> β} : mapDomain f (v₁ + v₂
) = mapDomain f v₁ + mapDomain f v₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomain_add (f : M → N) (x y : R[M]) :
    mapDomain f (x + y) = mapDomain f x + mapDomain f y := by
  ext; simp [Finsupp.mapDomain_add]

@[to_additive]
/-
**MonoidAlgebra.mapDomain_sum** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomain_sum (f : M -> N) (x : S[M]) (v : M -> S -> R[M]) : mapDomain f (
x.coeff.sum v) = x.coeff.sum fun a b => mapDomain f (v a b)
参数：f : M -> N；x : S[M]；v : M -> S -> R[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidAlgebra.coeff_mapDomain`：∀ {R : Type u_3} {M : Type u_6} {N : Type
 u_7} [inst : Semiring R] (f : M → N) (x : MonoidAlgebra R M),   (MonoidAlgebra.
mapDomain f x).coef…
· 使用引理 `MonoidAlgebra.coeff_finsuppSum`：coeff_finsuppSum [AddCommMonoid N] (f : 
ι ->₀ N) (g : ι -> N -> R[M]) : coeff (f.sum g) = f.sum (fun i n => coeff (g i n
))
· 使用定理 `Finsupp.mapDomain_sum`：mapDomain_sum [Zero N] {f : α -> β} {s : α ->₀ N}
 {v : α -> N -> α ->₀ M} : mapDomain f (s.sum v) = s.sum fun a b => mapDomain f 
(v a b)
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomain_sum (f : M → N) (x : S[M]) (v : M → S → R[M]) :
    mapDomain f (x.coeff.sum v) = x.coeff.sum fun a b ↦ mapDomain f (v a b) := by
  ext; simp [Finsupp.mapDomain_sum]

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapDomain_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomain_single : mapDomain f (single a r) = single (f a) r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.coeff_mapDomain`：∀ {R : Type u_3} {M : Type u_6} {N : Type
 u_7} [inst : Semiring R] (f : M → N) (x : MonoidAlgebra R M),   (MonoidAlgebra.
mapDomain f x).coef…
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomain_single : mapDomain f (single a r) = single (f a) r := by ext; simp

@[to_additive]
/-
**MonoidAlgebra.mapDomain_injective** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomain_injective (hf : Injective f) : Injective (mapDomain (R
参数：hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `MonoidAlgebra.ofCoeff_injective`：ofCoeff_injective : (ofCoeff : (M ->₀ R
) -> R[M]).Injective
· 使用定理 `Finsupp.mapDomain_injective`：mapDomain_injective {f : α -> β} (hf : Func
tion.Injective f) : Function.Injective (mapDomain f : (α ->₀ M) -> β ->₀ M)
· 使用引理 `MonoidAlgebra.coeff_injective`：coeff_injective : (coeff : R[M] -> M ->₀ 
R).Injective
-/
lemma mapDomain_injective (hf : Injective f) : Injective (mapDomain (R := R) f) :=
  ofCoeff_injective.comp <| (Finsupp.mapDomain_injective hf).comp coeff_injective

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := R) (attr := simp) mapDomain_one]
/-
**MonoidAlgebra.mapDomain_one** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomain_one [One M] [One N] {F : Type*} [FunLike F M N] [OneHomClass F M
 N] (f : F) : mapDomain f (1 : R[M]) = (1 : R[N])
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.mapDomain_single`：mapDomain_single : mapDomain f (single a
 r) = single (f a) r
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapDomain_one [One M] [One N] {F : Type*} [FunLike F M N] [OneHomClass F M N] (f : F) :
    mapDomain f (1 : R[M]) = (1 : R[N]) := by
  simp [one_def]

/-- Given a map `f : R →+ S`, return the corresponding map `R[M] → S[M]` obtained by mapping
each coefficient along `f`. -/
@[to_additive
/-- Given a map `f : R →+ S`, return the corresponding map `R[M] → S[M]` obtained by mapping
each coefficient along `f`. -/]
/-
**MonoidAlgebra.map** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：map (f : R ->+ S) (x : R[M]) : S[M]
参数：f : R ->+ S；x : R[M]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map (f : R →+ S) (x : R[M]) : S[M] := .ofCoeff <| x.coeff.mapRange f f.map_zero

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.coeff_map** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：coeff_map (f : R ->+ S) (x : R[M]) : (map f x).coeff = x.coeff.mapRange f 
f.map_zero
参数：f : R ->+ S；x : R[M]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeff_map (f : R →+ S) (x : R[M]) :
    (map f x).coeff = x.coeff.mapRange f f.map_zero := rfl

/-- This isn't marked as simp to avoid looping with unfolding `coeff`. -/
@[to_additive /-- This isn't marked as simp to avoid looping with unfolding `coeff`. -/]
/-
**MonoidAlgebra.ofCoeff_mapRange** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：ofCoeff_mapRange (f : R ->+ S) (x : M ->₀ R) : ofCoeff (.mapRange f f.map_
zero x) = map f (ofCoeff x)
参数：f : R ->+ S；x : M ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0

--- 原说明 ---
This isn't marked as simp to avoid looping with unfolding `coeff`.
-/
lemma ofCoeff_mapRange (f : R →+ S) (x : M →₀ R) :
    ofCoeff (.mapRange f f.map_zero x) = map f (ofCoeff x) := rfl

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：∀ {R : Type u_3} {S : Type u_4} {M : Type u_6} [inst : Semiring R] [inst_1
 : Semiring S] (f : R →+ S),   MonoidAlgebra.map f 0 = 0
参数：f : R →+ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapRange_zero`：mapRange_zero {f : M -> N} {hf : f 0 = 0} : mapRa
nge f hf (0 : α ->₀ M) = 0
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma map_zero (f : R →+ S) : map f (0 : R[M]) = 0 := by ext; simp

@[to_additive]
/-
**MonoidAlgebra.map_add** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：∀ {R : Type u_3} {S : Type u_4} {M : Type u_6} [inst : Semiring R] [inst_1
 : Semiring S] (f : R →+ S)   (x y : MonoidAlgebra R M), MonoidAlgebra.map f (x 
+ y) = MonoidAlgebra.map f x + MonoidAlgebra.map f y
参数：f : R →+ S；x y : MonoidAlgebra R M；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma map_add (f : R →+ S) (x y : R[M]) : map f (x + y) = map f x + map f y := by
  ext; simp

@[to_additive]
/-
**MonoidAlgebra.map_sum** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {S : Type u_4} {M : Type u_6} [inst : Semi
ring R] [inst_1 : Semiring S] (f : R →+ S)   (s : Finset ι) (x : ι → MonoidAlgeb
ra R M), MonoidAlgebra.map f (∑ i ∈ s, x i) = ∑ i ∈ s, MonoidAlgebra.map f (x i)
参数：f : R →+ S；s : Finset ι；x : ι → MonoidAlgebra R M；∑ i ∈ s, x i；x i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.mapRange.congr_simp`：∀ {α : Type u_1} {M : Type u_4} {N : Type u
_5} [inst : Zero M] [inst_1 : Zero N] (f f_1 : M → N) (e_f : f = f_1)   (hf : f 
0 = 0) (g g_1 : α…
· 使用引理 `MonoidAlgebra.coeff_sum`：coeff_sum (s : Finset ι) (f : ι -> R[M]) : coef
f (∑ i in s, f i) = ∑ i in s, coeff (f i)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_finsetSum`：∀ {α : Type u_1} {ι : Type u_2} {N : Type u_10} [
inst : AddCommMonoid N] (S : Finset ι) (f : ι → α →₀ N),   ⇑(∑ i ∈ S, f i) = ∑ i
 ∈ S, ⇑(f i…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma map_sum (f : R →+ S) (s : Finset ι) (x : ι → R[M]) :
    map f (∑ i ∈ s, x i) = ∑ i ∈ s, map f (x i) := by ext; simp

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.map_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：map_single (f : R ->+ S) (r : R) (m : M) : map f (single m r) = single m (
f r)
参数：f : R ->+ S；r : R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_single (f : R →+ S) (r : R) (m : M) : map f (single m r) = single m (f r) := by ext; simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**MonoidAlgebra.map_id** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：map_id (x : R[M]) : map (.id R) x = x
参数：x : R[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapRange_id`：mapRange_id (g : α ->₀ M) : mapRange id rfl g = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_id (x : R[M]) : map (.id R) x = x := by ext; simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**MonoidAlgebra.map_map** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：map_map (f : S ->+ T) (g : R ->+ S) (x : R[M]) : map f (map g x) = map (f.
comp g) x
参数：f : S ->+ T；g : R ->+ S；x : R[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用引理 `Finsupp.mapRange_mapRange`：mapRange_mapRange (e₁ : N -> O) (e₂ : M -> N)
 (he₁ he₂) (f : α ->₀ M) : mapRange e₁ he₁ (mapRange e₂ he₂ f) = mapRange (e₁ ∘ 
e₂) (by simp [*…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_map (f : S →+ T) (g : R →+ S) (x : R[M]) : map f (map g x) = map (f.comp g) x := by
  ext; simp

@[to_additive]
/-
**MonoidAlgebra.range_map** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：range_map (f : R ->+ S) : Set.range (map (M
参数：f : R ->+ S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonoidAlgebra.coeffEquiv_apply`：∀ {R : Type u_1} {M : Type u_4} [inst : 
Semiring R] (self : MonoidAlgebra R M),   MonoidAlgebra.coeffEquiv self = self.c
oeff
· 使用定理 `Finsupp.mapRange.congr_simp`：∀ {α : Type u_1} {M : Type u_4} {N : Type u
_5} [inst : Zero M] [inst_1 : Zero N] (f f_1 : M → N) (e_f : f = f_1)   (hf : f 
0 = 0) (g g_1 : α…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.range_comp`：∀ {ι : Sort u_1} {ι' : Sort u_2} {E : Type u_3} [i
nst : EquivLike E ι ι'] {α : Type u_4} (f : ι' → α) (e : E),   Set.range (f ∘ ⇑e
) = Set.ra…
· 使用引理 `Finsupp.range_mapRange`：range_mapRange (e : M -> N) (he₀ : e 0 = 0) : Se
t.range (Finsupp.mapRange (α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma range_map (f : R →+ S) : Set.range (map (M := M) f) = {x | ∀ i, x.coeff i ∈ Set.range f} :=
  calc
    _ = coeffEquiv ⁻¹' (Set.range (mapRange f (map_zero f) ∘ coeffEquiv)) := by
      simp_rw [comp_def, Equiv.eq_preimage_iff_image_eq, ← Set.range_comp', coeffEquiv_apply,
        coeff_map]
    _ = _ := by simp [Finsupp.range_mapRange]

/-- `MonoidAlgebra.map` of an injective function is injective. -/
@[to_additive /-- `AddMonoidAlgebra.map` of an injective function is injective. -/]
/-
**MonoidAlgebra.map_injective** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：map_injective (f : R ->+ S) (he : Injective f) : Injective (map (M
参数：f : R ->+ S；he : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用定理 `Finsupp.mapRange.congr_simp`：∀ {α : Type u_1} {M : Type u_4} {N : Type u
_5} [inst : Zero M] [inst_1 : Zero N] (f f_1 : M → N) (e_f : f = f_1)   (hf : f 
0 = 0) (g g_1 : α…
· 使用定理 `MonoidAlgebra.coeffEquiv_apply`：∀ {R : Type u_1} {M : Type u_4} [inst : 
Semiring R] (self : MonoidAlgebra R M),   MonoidAlgebra.coeffEquiv self = self.c
oeff
· 使用定理 `MonoidAlgebra.coeffEquiv_symm_apply`：∀ {R : Type u_1} {M : Type u_4} [in
st : Semiring R] (coeff : M →₀ R),   MonoidAlgebra.coeffEquiv.symm coeff = Monoi
dAlgebra.ofCoeff coeff
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用引理 `Finsupp.mapRange_injective`：mapRange_injective (e : M -> N) (he₀ : e 0 =
 0) (he : Injective e) : Injective (Finsupp.mapRange (α

--- 原说明 ---
`MonoidAlgebra.map` of an injective function is injective.
-/
lemma map_injective (f : R →+ S) (he : Injective f) : Injective (map (M := M) f) := by
  have : map (M := M) f = coeffEquiv.symm ∘ Finsupp.mapRange f (map_zero f) ∘ coeffEquiv := by
    ext; simp [ofCoeff_mapRange]
  simpa [this] using mapRange_injective _ (map_zero f) he

/-- `MonoidAlgebra.map` of a surjective function is surjective. -/
@[to_additive /-- `AddMonoidAlgebra.map` of an surjective function is surjective. -/]
/-
**MonoidAlgebra.map_surjective** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：map_surjective (f : R ->+ S) (he : Surjective f) : Surjective (map (M
参数：f : R ->+ S；he : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用定理 `Finsupp.mapRange.congr_simp`：∀ {α : Type u_1} {M : Type u_4} {N : Type u
_5} [inst : Zero M] [inst_1 : Zero N] (f f_1 : M → N) (e_f : f = f_1)   (hf : f 
0 = 0) (g g_1 : α…
· 使用定理 `MonoidAlgebra.coeffEquiv_apply`：∀ {R : Type u_1} {M : Type u_4} [inst : 
Semiring R] (self : MonoidAlgebra R M),   MonoidAlgebra.coeffEquiv self = self.c
oeff
· 使用定理 `MonoidAlgebra.coeffEquiv_symm_apply`：∀ {R : Type u_1} {M : Type u_4} [in
st : Semiring R] (coeff : M →₀ R),   MonoidAlgebra.coeffEquiv.symm coeff = Monoi
dAlgebra.ofCoeff coeff
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finsupp.mapRange_surjective`：mapRange_surjective (e : M -> N) (he₀ : e 0
 = 0) (he : Surjective e) : Surjective (Finsupp.mapRange (α

--- 原说明 ---
`MonoidAlgebra.map` of a surjective function is surjective.
-/
lemma map_surjective (f : R →+ S) (he : Surjective f) : Surjective (map (M := M) f) := by
  have : map (M := M) f = coeffEquiv.symm ∘ Finsupp.mapRange f (map_zero f) ∘ coeffEquiv := by
    ext; simp [ofCoeff_mapRange]
  simpa [this] using mapRange_surjective _ (map_zero f) he

/-- Pullback the coefficients of an element of `R[N]` under an injective `f : M → N`.

Coefficients not in the range of `f` are dropped. -/
@[to_additive
/-- Pullback the coefficients of an element of `R[N]` under an injective `f : M → N`.

Coefficients not in the range of `f` are dropped. -/]
/-
**MonoidAlgebra.comapDomain** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：comapDomain (f : M -> N) (hf : Injective f) (x : R[N]) : R[M]
参数：f : M -> N；hf : Injective f；x : R[N]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def comapDomain (f : M → N) (hf : Injective f) (x : R[N]) : R[M] :=
  .ofCoeff <| x.coeff.comapDomain f hf.injOn

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.coeff_comapDomain** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：coeff_comapDomain (f : M -> N) (hf) (x : R[N]) : (comapDomain f hf x).coef
f = x.coeff.comapDomain f hf.injOn
参数：f : M -> N；hf；x : R[N]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_comapDomain (f : M → N) (hf) (x : R[N]) :
    (comapDomain f hf x).coeff = x.coeff.comapDomain f hf.injOn := by simp [comapDomain]

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.comapDomain_zero** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：comapDomain_zero (f : M -> N) (hf) : comapDomain f hf (0 : R[N]) = 0
参数：f : M -> N；hf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用引理 `MonoidAlgebra.coeff_comapDomain`：coeff_comapDomain (f : M -> N) (hf) (x 
: R[N]) : (comapDomain f hf x).coeff = x.coeff.comapDomain f hf.injOn
· 使用定理 `Finsupp.comapDomain_zero`：comapDomain_zero (f : α -> β) (hif : Set.InjOn
 f (f ⁻¹' ↑(0 : β ->₀ M).support)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comapDomain_zero (f : M → N) (hf) : comapDomain f hf (0 : R[N]) = 0 := by ext; simp

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.comapDomain_add** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：comapDomain_add (f : M -> N) (hf) (x y : R[N]) : comapDomain f hf (x + y) 
= comapDomain f hf x + comapDomain f hf y
参数：f : M -> N；hf；x y : R[N]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用引理 `MonoidAlgebra.coeff_comapDomain`：coeff_comapDomain (f : M -> N) (hf) (x 
: R[N]) : (comapDomain f hf x).coeff = x.coeff.comapDomain f hf.injOn
· 使用定理 `Finsupp.comapDomain_add_of_injective`：comapDomain_add_of_injective (hf :
 Function.Injective f) (v₁ v₂ : β ->₀ M) : comapDomain f (v₁ + v₂) hf.injOn = co
mapDomain f v₁ hf.injOn + …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comapDomain_add (f : M → N) (hf) (x y : R[N]) :
    comapDomain f hf (x + y) = comapDomain f hf x + comapDomain f hf y := by
  ext; simp [comapDomain_add_of_injective hf]

@[simp]
/-
**MonoidAlgebra.comapDomain_single_of_not_mem_range** 是 Mathlib 中的一个引理，位于命名空间 `M
onoidAlgebra`。
形式化陈述：comapDomain_single_of_not_mem_range {r : R} {n : N} (hn : n ∉ Set.range f)
 (hf) : comapDomain f hf (single n r) = 0
参数：hn : n ∉ Set.range f；hf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用引理 `MonoidAlgebra.coeff_comapDomain`：coeff_comapDomain (f : M -> N) (hf) (x 
: R[N]) : (comapDomain f hf x).coeff = x.coeff.comapDomain f hf.injOn
· 使用引理 `Finsupp.comapDomain_single_of_not_mem_range`：comapDomain_single_of_not_m
em_range [Zero M] {f : α -> β} {b : β} (hb : b ∉ Set.range f) (m : M) (hf) : com
apDomain f (single b m) hf = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comapDomain_single_of_not_mem_range {r : R} {n : N} (hn : n ∉ Set.range f) (hf) :
    comapDomain f hf (single n r) = 0 := by ext; simp [*]

/-- `comapDomain` as an `AddMonoidHom`. -/
@[to_additive (attr := simps) comapDomainAddMonoidHom /-- `comapDomain` as an `AddMonoidHom`. -/]
/-
**MonoidAlgebra.comapDomainAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra
`。
形式化陈述：comapDomainAddMonoidHom (f : M -> N) (hf : Injective f) : R[N] ->+ R[M] wh
ere toFun
参数：f : M -> N；hf : Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`comapDomain` as an `AddMonoidHom`.
-/
def comapDomainAddMonoidHom (f : M → N) (hf : Injective f) : R[N] →+ R[M] where
  toFun := comapDomain f hf
  map_zero' := by simp
  map_add' := by simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**MonoidAlgebra.comapDomain_single_map** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`
。
形式化陈述：comapDomain_single_map (f : M -> N) (hf) (m : M) (r : R) : comapDomain f h
f (single (f m) r) = single m r
参数：f : M -> N；hf；m : M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用引理 `MonoidAlgebra.coeff_comapDomain`：coeff_comapDomain (f : M -> N) (hf) (x 
: R[N]) : (comapDomain f hf x).coeff = x.coeff.comapDomain f hf.injOn
· 使用定理 `Finsupp.comapDomain_single`：comapDomain_single (f : α -> β) (a : α) (m :
 M) (hif : Set.InjOn f (f ⁻¹' (single (f a) m).support)) : comapDomain f (Finsup
p.single (f a) m…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comapDomain_single_map (f : M → N) (hf) (m : M) (r : R) :
    comapDomain f hf (single (f m) r) = single m r := by ext; simp

@[to_additive]
/-
**MonoidAlgebra.mapDomain_comapDomain** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomain_comapDomain {f : M -> N} {x : R[N]} (hx : ↑x.coeff.support subse
teq Set.range f) (hf) : mapDomain f (comapDomain f hf x) = x
参数：hx : ↑x.coeff.support subseteq Set.range f；hf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.mapDomain_comapDomain`：mapDomain_comapDomain (hf : Function.Inje
ctive f) (l : β ->₀ M) (hl : ↑l.support subseteq Set.range f) : mapDomain f (com
apDomain f l hf.inj…
-/
lemma mapDomain_comapDomain {f : M → N} {x : R[N]} (hx : ↑x.coeff.support ⊆ Set.range f) (hf) :
    mapDomain f (comapDomain f hf x) = x := by
  ext : 1; exact Finsupp.mapDomain_comapDomain _ hf _ hx

section Mul
variable [Mul M] [Mul N] [Mul O] [FunLike F M N] [MulHomClass F M N]

@[to_additive (dont_translate := R) mapDomain_mul]
/-
**MonoidAlgebra.mapDomain_mul** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomain_mul (f : F) (x y : R[M]) : mapDomain f (x * y) = mapDomain f x *
 mapDomain f y
参数：f : F；x y : R[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.mul_def`：mul_def (x y : R[M]) : x * y = x.coeff.sum fun m₁
 r₁ => y.coeff.sum fun m₂ r₂ => single (m₁ * m₂) (r₁ * r₂)
· 使用引理 `MonoidAlgebra.mapDomain_sum`：mapDomain_sum (f : M -> N) (x : S[M]) (v : 
M -> S -> R[M]) : mapDomain f (x.coeff.sum v) = x.coeff.sum fun a b => mapDomain
 f (v a b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MonoidAlgebra.mapDomain_single`：mapDomain_single : mapDomain f (single a
 r) = single (f a) r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidAlgebra.coeff_mapDomain`：∀ {R : Type u_3} {M : Type u_6} {N : Type
 u_7} [inst : Semiring R] (f : M → N) (x : MonoidAlgebra R M),   (MonoidAlgebra.
mapDomain f x).coef…
· 使用定理 `Finsupp.sum_mapDomain_index`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f : α 
→ β} {s : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `MonoidAlgebra.single_zero`：single_zero (m : M) : (single m 0 : R[M]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用引理 `MonoidAlgebra.single_add`：single_add (m : M) (r₁ r₂ : R) : single m (r₁ 
+ r₂) = single m r₁ + single m r₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finsupp.sum_fun_zero`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M),   (f.sum fun x x_1 => 0) 
= 0
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Finsupp.sum_add`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst :
 Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M}   {h₁ h₂ : α → M → N}, (f.sum f
un a …
-/
lemma mapDomain_mul (f : F) (x y : R[M]) : mapDomain f (x * y) = mapDomain f x * mapDomain f y := by
  simp [mul_def, mapDomain_sum, add_mul, mul_add, sum_mapDomain_index]

variable (R) in
/-- If `f : G → H` is a multiplicative homomorphism between two monoids, then
`MonoidAlgebra.mapDomain f` is a ring homomorphism between their monoid algebras. -/
@[to_additive (attr := simps) /--
If `f : G → H` is a multiplicative homomorphism between two additive monoids, then
`AddMonoidAlgebra.mapDomain f` is a ring homomorphism between their additive monoid algebras. -/]
/-
**MonoidAlgebra.mapDomainNonUnitalRingHom** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgeb
ra`。
形式化陈述：mapDomainNonUnitalRingHom (f : M ->ₙ* N) : R[M] ->ₙ+* R[N] where toFun
参数：f : M ->ₙ* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapDomainNonUnitalRingHom (f : M →ₙ* N) : R[M] →ₙ+* R[N] where
  toFun := mapDomain f
  map_zero' := mapDomain_zero _
  map_add' := mapDomain_add _
  map_mul' := mapDomain_mul f

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := R) (attr := simp)]
/-
**MonoidAlgebra.mapDomainNonUnitalRingHom_id** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAl
gebra`。
形式化陈述：mapDomainNonUnitalRingHom_id : mapDomainNonUnitalRingHom R (.id M) = .id R
[M]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.mapDomainNonUnitalRingHom_apply`：∀ (R : Type u_3) {M : Typ
e u_6} {N : Type u_7} [inst : Semiring R] [inst_1 : Mul M] [inst_2 : Mul N] (f :
 M →ₙ* N)   (x : MonoidAlgebra R M)…
· 使用定理 `MonoidAlgebra.coeff_mapDomain`：∀ {R : Type u_3} {M : Type u_6} {N : Type
 u_7} [inst : Semiring R] (f : M → N) (x : MonoidAlgebra R M),   (MonoidAlgebra.
mapDomain f x).coef…
· 使用定理 `Finsupp.mapDomain_id`：mapDomain_id : mapDomain id v = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainNonUnitalRingHom_id : mapDomainNonUnitalRingHom R (.id M) = .id R[M] := by ext; simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := R) (attr := simp)]
/-
**MonoidAlgebra.mapDomainNonUnitalRingHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `Monoid
Algebra`。
形式化陈述：mapDomainNonUnitalRingHom_comp (f : N ->ₙ* O) (g : M ->ₙ* N) : mapDomainNo
nUnitalRingHom R (f.comp g) = (mapDomainNonUnitalRingHom R f).comp (mapDomainNon
UnitalRingHom R g)
参数：f : N ->ₙ* O；g : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidAlgebra.mapDomainNonUnitalRingHom_apply`：∀ (R : Type u_3) {M : Typ
e u_6} {N : Type u_7} [inst : Semiring R] [inst_1 : Mul M] [inst_2 : Mul N] (f :
 M →ₙ* N)   (x : MonoidAlgebra R M)…
· 使用定理 `MonoidAlgebra.coeff_mapDomain`：∀ {R : Type u_3} {M : Type u_6} {N : Type
 u_7} [inst : Semiring R] (f : M → N) (x : MonoidAlgebra R M),   (MonoidAlgebra.
mapDomain f x).coef…
· 使用定理 `Finsupp.mapDomain_comp`：mapDomain_comp {f : α -> β} {g : β -> γ} : mapDo
main (g ∘ f) v = mapDomain g (mapDomain f v)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainNonUnitalRingHom_comp (f : N →ₙ* O) (g : M →ₙ* N) :
    mapDomainNonUnitalRingHom R (f.comp g) =
      (mapDomainNonUnitalRingHom R f).comp (mapDomainNonUnitalRingHom R g) := by
  ext; simp [Finsupp.mapDomain_comp]

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- Equivalent monoids have additively isomorphic monoid algebras.

`MonoidAlgebra.mapDomain` as an `AddEquiv`. -/
@[to_additive (dont_translate := R)
/-- Equivalent additive monoids have additively isomorphic additive monoid algebras.

`AddMonoidAlgebra.mapDomain` as an `AddEquiv`. -/]
/-
**MonoidAlgebra.mapDomainAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomainAddEquiv (e : M ≃ N) : R[M] ≃+ R[N] where toFun x
参数：e : M ≃ N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def mapDomainAddEquiv (e : M ≃ N) : R[M] ≃+ R[N] where
  toFun x := x.mapDomain e
  invFun x := x.mapDomain e.symm
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**MonoidAlgebra.coeff_mapDomainAddEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra
`。
形式化陈述：coeff_mapDomainAddEquiv (e : M ≃ N) (x : R[M]) : (mapDomainAddEquiv R e x)
.coeff = equivMapDomain e x.coeff
参数：e : M ≃ N；x : R[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.coeff_mapDomain`：∀ {R : Type u_3} {M : Type u_6} {N : Type
 u_7} [inst : Semiring R] (f : M → N) (x : MonoidAlgebra R M),   (MonoidAlgebra.
mapDomain f x).coef…
· 使用定理 `Finsupp.mapDomain_equiv_apply`：mapDomain_equiv_apply {f : α ≃ β} (x : α 
->₀ M) (a : β) : mapDomain f x a = x (f.symm a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_mapDomainAddEquiv (e : M ≃ N) (x : R[M]) :
    (mapDomainAddEquiv R e x).coeff = equivMapDomain e x.coeff := by ext; simp [mapDomainAddEquiv]

@[deprecated (since := "2026-06-18")] alias mapDomainAddEquiv_apply := coeff_mapDomainAddEquiv

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapDomainAddEquiv_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebr
a`。
形式化陈述：mapDomainAddEquiv_single (e : M ≃ N) (r : R) (m : M) : mapDomainAddEquiv R
 e (single m r) = single (e m) r
参数：e : M ≃ N；r : R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.mapDomain_single`：mapDomain_single : mapDomain f (single a
 r) = single (f a) r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainAddEquiv_single (e : M ≃ N) (r : R) (m : M) :
    mapDomainAddEquiv R e (single m r) = single (e m) r := by simp [mapDomainAddEquiv]

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.symm_mapDomainAddEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`
。
形式化陈述：symm_mapDomainAddEquiv (e : M ≃ N) : (mapDomainAddEquiv R e).symm = mapDom
ainAddEquiv R e.symm
参数：e : M ≃ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_mapDomainAddEquiv (e : M ≃ N) :
    (mapDomainAddEquiv R e).symm = mapDomainAddEquiv R e.symm := rfl

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapDomainAddEquiv_trans** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra
`。
形式化陈述：mapDomainAddEquiv_trans (e₁ : M ≃ N) (e₂ : N ≃ O) : mapDomainAddEquiv R (e
₁.trans e₂) = (mapDomainAddEquiv R e₁).trans (mapDomainAddEquiv R e₂)
参数：e₁ : M ≃ N；e₂ : N ≃ O。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst_1 : A
dd N] {f g : M ≃+ N}, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MonoidAlgebra.coeff_mapDomainAddEquiv`：coeff_mapDomainAddEquiv (e : M ≃ 
N) (x : R[M]) : (mapDomainAddEquiv R e x).coeff = equivMapDomain e x.coeff
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainAddEquiv_trans (e₁ : M ≃ N) (e₂ : N ≃ O) :
    mapDomainAddEquiv R (e₁.trans e₂) =
      (mapDomainAddEquiv R e₁).trans (mapDomainAddEquiv R e₂) := by ext; simp

variable (M) in
/-- Additively isomorphic rings have additively isomorphic monoid algebras.

`MonoidAlgebra.map` as an `AddEquiv`. -/
@[to_additive (dont_translate := R S)
/-- Additively isomorphic rings have additively isomorphic additive monoid algebras.

`AddMonoidAlgebra.map` as an `AddEquiv`. -/]
/-
**MonoidAlgebra.mapAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapAddEquiv (e : R ≃+ S) : R[M] ≃+ S[M] where toFun
参数：e : R ≃+ S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapAddEquiv (e : R ≃+ S) : R[M] ≃+ S[M] where
  toFun := .map e
  invFun := .map e.symm
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' := MonoidAlgebra.map_add _

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv := mapAddEquiv

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**MonoidAlgebra.coeff_mapAddEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：coeff_mapAddEquiv (e : R ≃+ S) (x : R[M]) (m : M) : (mapAddEquiv M e x).co
eff m = e (x.coeff m)
参数：e : R ≃+ S；x : R[M]；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_mapAddEquiv (e : R ≃+ S) (x : R[M]) (m : M) :
    (mapAddEquiv M e x).coeff m = e (x.coeff m) := by simp [mapAddEquiv]

@[deprecated (since := "2026-06-18")] alias mapAddEquiv_apply := coeff_mapAddEquiv

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv_apply := coeff_mapAddEquiv

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapAddEquiv_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapAddEquiv_single (e : R ≃+ S) (r : R) (m : M) : mapAddEquiv M e (single 
m r) = single m (e r)
参数：e : R ≃+ S；r : R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.map_single`：map_single (f : R ->+ S) (r : R) (m : M) : map
 f (single m r) = single m (f r)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapAddEquiv_single (e : R ≃+ S) (r : R) (m : M) :
    mapAddEquiv M e (single m r) = single m (e r) := by simp [mapAddEquiv]

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv_single := mapAddEquiv_single

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.symm_mapAddEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：symm_mapAddEquiv (e : R ≃+ S) : (mapAddEquiv M e).symm = mapAddEquiv M e.s
ymm
参数：e : R ≃+ S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_mapAddEquiv (e : R ≃+ S) :
    (mapAddEquiv M e).symm = mapAddEquiv M e.symm := rfl

@[deprecated (since := "2026-03-20")] alias symm_mapRangeAddEquiv := symm_mapAddEquiv

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapAddEquiv_trans** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapAddEquiv_trans (e₁ : R ≃+ S) (e₂ : S ≃+ T) : mapAddEquiv M (e₁.trans e₂
) = (mapAddEquiv M e₁).trans (mapAddEquiv M e₂)
参数：e₁ : R ≃+ S；e₂ : S ≃+ T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst_1 : A
dd N] {f g : M ≃+ N}, (∀ (x : M), f x = g x) → f = g
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.coeff_mapAddEquiv`：coeff_mapAddEquiv (e : R ≃+ S) (x : R[M
]) (m : M) : (mapAddEquiv M e x).coeff m = e (x.coeff m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapAddEquiv_trans (e₁ : R ≃+ S) (e₂ : S ≃+ T) :
    mapAddEquiv M (e₁.trans e₂) = (mapAddEquiv M e₁).trans (mapAddEquiv M e₂) := by
  ext; simp

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv_trans := mapAddEquiv_trans

@[to_additive (attr := simp) (dont_translate := R S) map_mul]
/-
**MonoidAlgebra.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：∀ {R : Type u_3} {S : Type u_4} {M : Type u_6} [inst : Semiring R] [inst_1
 : Semiring S] [inst_2 : Mul M] (f : R →+* S)   (x y : MonoidAlgebra R M), Monoi
dAlgebra.map (↑f) (x * y) = MonoidAlgebra.map (↑f) x * MonoidAlgebra.map (↑f) y
参数：f : R →+* S；x y : MonoidAlgebra R M；↑f；x * y；↑f；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MonoidAlgebra.mul_def`：mul_def (x y : R[M]) : x * y = x.coeff.sum fun m₁
 r₁ => y.coeff.sum fun m₂ r₂ => single (m₁ * m₂) (r₁ * r₂)
· 使用定理 `Finsupp.mapRange.congr_simp`：∀ {α : Type u_1} {M : Type u_4} {N : Type u
_5} [inst : Zero M] [inst_1 : Zero N] (f f_1 : M → N) (e_f : f = f_1)   (hf : f 
0 = 0) (g g_1 : α…
· 使用引理 `MonoidAlgebra.coeff_finsuppSum`：coeff_finsuppSum [AddCommMonoid N] (f : 
ι ->₀ N) (g : ι -> N -> R[M]) : coeff (f.sum g) = f.sum (fun i n => coeff (g i n
))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Finsupp.sum_mapRange_index`：∀ {α : Type u_1} {M : Type u_8} {M' : Type u
_9} {N : Type u_10} [inst : Zero M] [inst_1 : Zero M']   [inst_2 : AddCommMonoid
 N] {f : M → M'}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `MonoidAlgebra.single_zero`：single_zero (m : M) : (single m 0 : R[M]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
（共 32 条，此处仅展示前 30 条）
-/
protected lemma map_mul (f : R →+* S) (x y : R[M]) :
    map (f : R →+ S) (x * y) = map f x * map f y := by
  classical
  ext
  simp [mul_def, sum_mapRange_index, map_finsuppSum, single_apply, apply_ite]

end Mul

variable [Monoid M] [Monoid N] [Monoid O]

variable (R) in
/-- If `f : G → H` is a multiplicative homomorphism between two monoids, then
`MonoidAlgebra.mapDomain f` is a ring homomorphism between their monoid algebras. -/
@[to_additive (attr := simps) /--
If `f : G → H` is a multiplicative homomorphism between two additive monoids, then
`AddMonoidAlgebra.mapDomain f` is a ring homomorphism between their additive monoid algebras. -/]
/-
**MonoidAlgebra.mapDomainRingHom** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomainRingHom (f : M ->* N) : R[M] ->+* R[N] where toFun
参数：f : M ->* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapDomainRingHom (f : M →* N) : R[M] →+* R[N] where
  toFun := mapDomain f
  map_zero' := mapDomain_zero _
  map_add' := mapDomain_add _
  map_one' := mapDomain_one f
  map_mul' := mapDomain_mul f

attribute [local ext high] ringHom_ext

@[to_additive (dont_translate := R) (attr := simp)]
/-
**MonoidAlgebra.mapDomainRingHom_id** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomainRingHom_id : mapDomainRingHom R (.id M) = .id R[M]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.ringHom_ext`：ringHom_ext [Semiring S] {f g : R[M] ->+* S} 
(h₁ : forall r, f (single 1 r) = g (single 1 r)) (h_of : forall m, f (single m 1
) = g (single m…
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.mapDomainRingHom_apply`：∀ (R : Type u_3) {M : Type u_6} {N
 : Type u_7} [inst : Semiring R] [inst_1 : Monoid M] [inst_2 : Monoid N] (f : M 
→* N)   (x : MonoidAlgebra…
· 使用引理 `MonoidAlgebra.mapDomain_single`：mapDomain_single : mapDomain f (single a
 r) = single (f a) r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainRingHom_id : mapDomainRingHom R (.id M) = .id R[M] := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := R) (attr := simp)]
/-
**MonoidAlgebra.mapDomainRingHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomainRingHom_comp (f : N ->* O) (g : M ->* N) : mapDomainRingHom R (f.
comp g) = (mapDomainRingHom R f).comp (mapDomainRingHom R g)
参数：f : N ->* O；g : M ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.ringHom_ext`：ringHom_ext [Semiring S] {f g : R[M] ->+* S} 
(h₁ : forall r, f (single 1 r) = g (single 1 r)) (h_of : forall m, f (single m 1
) = g (single m…
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidAlgebra.mapDomainRingHom_apply`：∀ (R : Type u_3) {M : Type u_6} {N
 : Type u_7} [inst : Semiring R] [inst_1 : Monoid M] [inst_2 : Monoid N] (f : M 
→* N)   (x : MonoidAlgebra…
· 使用引理 `MonoidAlgebra.mapDomain_single`：mapDomain_single : mapDomain f (single a
 r) = single (f a) r
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainRingHom_comp (f : N →* O) (g : M →* N) :
    mapDomainRingHom R (f.comp g) = (mapDomainRingHom R f).comp (mapDomainRingHom R g) := by
  ext <;> simp

@[to_additive (attr := simp) (dont_translate := R S) map_one]
/-
**MonoidAlgebra.map_one** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：∀ {R : Type u_3} {S : Type u_4} {M : Type u_6} [inst : Semiring R] [inst_1
 : Semiring S] [inst_2 : Monoid M]   (f : R →+* S), MonoidAlgebra.map (↑f) 1 = 1
参数：f : R →+* S；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.map_single`：map_single (f : R ->+ S) (r : R) (m : M) : map
 f (single m r) = single m (f r)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma map_one (f : R →+* S) : map f (1 : R[M]) = (1 : S[M]) := by ext; simp [one_def]

variable (M) in
/-- The ring homomorphism of monoid algebras induced by a homomorphism of the base rings. -/
@[to_additive (dont_translate := R S)
/-- The ring homomorphism of additive monoid algebras induced by a homomorphism of the base rings.
-/]
/-
**MonoidAlgebra.mapRingHom** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapRingHom (f : R ->+* S) : R[M] ->+* S[M] where toFun
参数：f : R ->+* S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.map_one`：∀ {R : Type u_3} {S : Type u_4} {M : Type u_6} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : Monoid M]   (f : R →+* S), Mon
oidAlgebra.…
-/
noncomputable def mapRingHom (f : R →+* S) : R[M] →+* S[M] where
  toFun := .map f
  map_zero' := MonoidAlgebra.map_zero _
  map_add' := MonoidAlgebra.map_add _
  map_one' := MonoidAlgebra.map_one _
  map_mul' := MonoidAlgebra.map_mul _

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom := mapRingHom

@[to_additive]
/-
**MonoidAlgebra.coe_mapRingHom** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：coe_mapRingHom (f : R ->+* S) : ⇑(mapRingHom M f) = map f
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mapRingHom (f : R →+* S) : ⇑(mapRingHom M f) = map f := rfl

@[deprecated (since := "2026-03-20")] alias coe_mapRangeRingHom := coe_mapRingHom

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**MonoidAlgebra.coeff_mapRingHom** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：coeff_mapRingHom (f : R ->+* S) (x : R[M]) (m : M) : (mapRingHom M f x).co
eff m = f (x.coeff m)
参数：f : R ->+* S；x : R[M]；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_mapRingHom (f : R →+* S) (x : R[M]) (m : M) :
    (mapRingHom M f x).coeff m = f (x.coeff m) := by simp [mapRingHom]

@[deprecated (since := "2026-06-18")] alias mapRingHom_apply := coeff_mapRingHom

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_apply := coeff_mapRingHom

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapRingHom_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapRingHom_single (f : R ->+* S) (a : M) (b : R) : mapRingHom M f (single 
a b) = single a (f b)
参数：f : R ->+* S；a : M；b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.map_single`：map_single (f : R ->+ S) (r : R) (m : M) : map
 f (single m r) = single m (f r)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapRingHom_single (f : R →+* S) (a : M) (b : R) :
    mapRingHom M f (single a b) = single a (f b) := by simp [mapRingHom]

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_single := mapRingHom_single

@[to_additive (dont_translate := R) (attr := simp)]
/-
**MonoidAlgebra.mapRingHom_id** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapRingHom_id : mapRingHom M (.id R) = .id R[M]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.ringHom_ext`：ringHom_ext [Semiring S] {f g : R[M] ->+* S} 
(h₁ : forall r, f (single 1 r) = g (single 1 r)) (h_of : forall m, f (single m 1
) = g (single m…
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.mapRingHom_single`：mapRingHom_single (f : R ->+* S) (a : M
) (b : R) : mapRingHom M f (single a b) = single a (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapRingHom_id : mapRingHom M (.id R) = .id R[M] := by ext <;> simp

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_id := mapRingHom_id

@[to_additive (dont_translate := R S T) (attr := simp)]
/-
**MonoidAlgebra.mapRingHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapRingHom_comp (f : S ->+* T) (g : R ->+* S) : mapRingHom M (f.comp g) = 
(mapRingHom M f).comp (mapRingHom M g)
参数：f : S ->+* T；g : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.ringHom_ext`：ringHom_ext [Semiring S] {f g : R[M] ->+* S} 
(h₁ : forall r, f (single 1 r) = g (single 1 r)) (h_of : forall m, f (single m 1
) = g (single m…
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MonoidAlgebra.mapRingHom_single`：mapRingHom_single (f : R ->+* S) (a : M
) (b : R) : mapRingHom M f (single a b) = single a (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma mapRingHom_comp (f : S →+* T) (g : R →+* S) :
    mapRingHom M (f.comp g) = (mapRingHom M f).comp (mapRingHom M g) := by
  ext <;> simp

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_comp := mapRingHom_comp

@[to_additive (dont_translate := R S)]
/-
**MonoidAlgebra.mapRingHom_comp_mapDomainRingHom** 是 Mathlib 中的一个引理，位于命名空间 `Mono
idAlgebra`。
形式化陈述：mapRingHom_comp_mapDomainRingHom (f : R ->+* S) (g : M ->* N) : (mapRingHo
m N f).comp (mapDomainRingHom R g) = (mapDomainRingHom S g).comp (mapRingHom M f
)
参数：f : R ->+* S；g : M ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.ringHom_ext`：ringHom_ext [Semiring S] {f g : R[M] ->+* S} 
(h₁ : forall r, f (single 1 r) = g (single 1 r)) (h_of : forall m, f (single m 1
) = g (single m…
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidAlgebra.mapDomainRingHom_apply`：∀ (R : Type u_3) {M : Type u_6} {N
 : Type u_7} [inst : Semiring R] [inst_1 : Monoid M] [inst_2 : Monoid N] (f : M 
→* N)   (x : MonoidAlgebra…
· 使用引理 `MonoidAlgebra.mapDomain_single`：mapDomain_single : mapDomain f (single a
 r) = single (f a) r
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `MonoidAlgebra.mapRingHom_single`：mapRingHom_single (f : R ->+* S) (a : M
) (b : R) : mapRingHom M f (single a b) = single a (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma mapRingHom_comp_mapDomainRingHom (f : R →+* S) (g : M →* N) :
    (mapRingHom N f).comp (mapDomainRingHom R g) =
      (mapDomainRingHom S g).comp (mapRingHom M f) := by aesop

@[deprecated (since := "2026-03-20")]
alias mapRangeRingHom_comp_mapDomainRingHom := mapRingHom_comp_mapDomainRingHom

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[to_additive (dont_translate := R)
/-- Isomorphic monoids have isomorphic additive monoid algebras. -/]
/-
**MonoidAlgebra.mapDomainRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomainRingEquiv (e : M ≃* N) : R[M] ≃+* R[N]
参数：e : M ≃* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapDomainRingEquiv (e : M ≃* N) : R[M] ≃+* R[N] :=
  .ofRingHom (MonoidAlgebra.mapDomainRingHom R e) (MonoidAlgebra.mapDomainRingHom R e.symm)
    (by apply MonoidAlgebra.ringHom_ext <;> simp) (by apply MonoidAlgebra.ringHom_ext <;> simp)

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.coeff_mapDomainRingEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebr
a`。
形式化陈述：coeff_mapDomainRingEquiv (e : M ≃* N) (x : R[M]) : (mapDomainRingEquiv R e
 x).coeff = equivMapDomain e x.coeff
参数：e : M ≃* N；x : R[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.coeff_mapDomainAddEquiv`：coeff_mapDomainAddEquiv (e : M ≃ 
N) (x : R[M]) : (mapDomainAddEquiv R e x).coeff = equivMapDomain e x.coeff
-/
lemma coeff_mapDomainRingEquiv (e : M ≃* N) (x : R[M]) :
    (mapDomainRingEquiv R e x).coeff = equivMapDomain e x.coeff := coeff_mapDomainAddEquiv ..

@[deprecated (since := "2026-06-18")] alias mapDomainRingEquiv_apply := coeff_mapDomainRingEquiv

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapDomainRingEquiv_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgeb
ra`。
形式化陈述：mapDomainRingEquiv_single (e : M ≃* N) (r : R) (m : M) : mapDomainRingEqui
v R e (single m r) = single (e m) r
参数：e : M ≃* N；r : R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.ofRingHom_apply`：∀ {R : Type u_4} {S : Type u_5} [inst : NonAs
socSemiring R] [inst_1 : NonAssocSemiring S] (f : R →+* S) (g : S →+* R)   (h₁ :
 f.comp g = Rin…
· 使用定理 `MonoidAlgebra.mapDomainRingHom_apply`：∀ (R : Type u_3) {M : Type u_6} {N
 : Type u_7} [inst : Semiring R] [inst_1 : Monoid M] [inst_2 : Monoid N] (f : M 
→* N)   (x : MonoidAlgebra…
· 使用引理 `MonoidAlgebra.mapDomain_single`：mapDomain_single : mapDomain f (single a
 r) = single (f a) r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainRingEquiv_single (e : M ≃* N) (r : R) (m : M) :
    mapDomainRingEquiv R e (single m r) = single (e m) r := by simp [mapDomainRingEquiv]

@[to_additive]
/-
**MonoidAlgebra.toRingHom_mapDomainRingEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAl
gebra`。
形式化陈述：toRingHom_mapDomainRingEquiv (e : M ≃* N) : (mapDomainRingEquiv R e).toRin
gHom = mapDomainRingHom R e
参数：e : M ≃* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toRingHom_mapDomainRingEquiv (e : M ≃* N) :
    (mapDomainRingEquiv R e).toRingHom = mapDomainRingHom R e := rfl

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.symm_mapDomainRingEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra
`。
形式化陈述：symm_mapDomainRingEquiv (e : M ≃* N) : (mapDomainRingEquiv R e).symm = map
DomainRingEquiv R e.symm
参数：e : M ≃* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_mapDomainRingEquiv (e : M ≃* N) :
    (mapDomainRingEquiv R e).symm = mapDomainRingEquiv R e.symm := rfl

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapDomainRingEquiv_trans** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebr
a`。
形式化陈述：mapDomainRingEquiv_trans (e₁ : M ≃* N) (e₂ : N ≃* O) : mapDomainRingEquiv 
R (e₁.trans e₂) = (mapDomainRingEquiv R e₁).trans (mapDomainRingEquiv R e₂)
参数：e₁ : M ≃* N；e₂ : N ≃* O。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MonoidAlgebra.coeff_mapDomainRingEquiv`：coeff_mapDomainRingEquiv (e : M 
≃* N) (x : R[M]) : (mapDomainRingEquiv R e x).coeff = equivMapDomain e x.coeff
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainRingEquiv_trans (e₁ : M ≃* N) (e₂ : N ≃* O) :
    mapDomainRingEquiv R (e₁.trans e₂) =
      (mapDomainRingEquiv R e₁).trans (mapDomainRingEquiv R e₂) := by ext; simp

variable (M) in
/-- Isomorphic rings have isomorphic monoid algebras. -/
@[to_additive (dont_translate := R S)
/-- Isomorphic rings have isomorphic additive monoid algebras. -/]
/-
**MonoidAlgebra.mapRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapRingEquiv (e : R ≃+* S) : R[M] ≃+* S[M]
参数：e : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapRingEquiv (e : R ≃+* S) : R[M] ≃+* S[M] :=
  .ofRingHom (MonoidAlgebra.mapRingHom M e) (MonoidAlgebra.mapRingHom M e.symm)
    (by apply MonoidAlgebra.ringHom_ext <;> simp) (by apply MonoidAlgebra.ringHom_ext <;> simp)

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv := mapRingEquiv

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.coeff_mapRingEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：coeff_mapRingEquiv (e : R ≃+* S) (x : R[M]) (m : M) : (mapRingEquiv M e x)
.coeff m = e (x.coeff m)
参数：e : R ≃+* S；x : R[M]；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.ofRingHom_apply`：∀ {R : Type u_4} {S : Type u_5} [inst : NonAs
socSemiring R] [inst_1 : NonAssocSemiring S] (f : R →+* S) (g : S →+* R)   (h₁ :
 f.comp g = Rin…
· 使用引理 `MonoidAlgebra.coeff_mapRingHom`：coeff_mapRingHom (f : R ->+* S) (x : R[M
]) (m : M) : (mapRingHom M f x).coeff m = f (x.coeff m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_mapRingEquiv (e : R ≃+* S) (x : R[M]) (m : M) :
    (mapRingEquiv M e x).coeff m = e (x.coeff m) := by simp [mapRingEquiv]

@[deprecated (since := "2026-06-18")] alias mapRingEquiv_apply := coeff_mapRingEquiv

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv_apply := coeff_mapRingEquiv

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapRingEquiv_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapRingEquiv_single (e : R ≃+* S) (r : R) (m : M) : mapRingEquiv M e (sing
le m r) = single m (e r)
参数：e : R ≃+* S；r : R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.ofRingHom_apply`：∀ {R : Type u_4} {S : Type u_5} [inst : NonAs
socSemiring R] [inst_1 : NonAssocSemiring S] (f : R →+* S) (g : S →+* R)   (h₁ :
 f.comp g = Rin…
· 使用引理 `MonoidAlgebra.mapRingHom_single`：mapRingHom_single (f : R ->+* S) (a : M
) (b : R) : mapRingHom M f (single a b) = single a (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapRingEquiv_single (e : R ≃+* S) (r : R) (m : M) :
    mapRingEquiv M e (single m r) = single m (e r) := by simp [mapRingEquiv]

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv_single := mapRingEquiv_single

@[to_additive]
/-
**MonoidAlgebra.toRingHom_mapRingEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`
。
形式化陈述：toRingHom_mapRingEquiv (e : R ≃+* S) : (mapRingEquiv M e).toRingHom = mapR
ingHom M e
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toRingHom_mapRingEquiv (e : R ≃+* S) :
    (mapRingEquiv M e).toRingHom = mapRingHom M e := rfl

@[deprecated (since := "2026-03-20")]
alias toRingHom_mapRangeRingEquiv := toRingHom_mapRingEquiv

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.symm_mapRingEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：symm_mapRingEquiv (e : R ≃+* S) : (mapRingEquiv M e).symm = mapRingEquiv M
 e.symm
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_mapRingEquiv (e : R ≃+* S) :
    (mapRingEquiv M e).symm = mapRingEquiv M e.symm := rfl

@[deprecated (since := "2026-03-20")] alias symm_mapRangeRingEquiv := symm_mapRingEquiv

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapRingEquiv_trans** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapRingEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* T) : mapRingEquiv M (e₁.tran
s e₂) = (mapRingEquiv M e₁).trans (mapRingEquiv M e₂)
参数：e₁ : R ≃+* S；e₂ : S ≃+* T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.coeff_mapRingEquiv`：coeff_mapRingEquiv (e : R ≃+* S) (x : 
R[M]) (m : M) : (mapRingEquiv M e x).coeff m = e (x.coeff m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapRingEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* T) :
    mapRingEquiv M (e₁.trans e₂) =
      (mapRingEquiv M e₁).trans (mapRingEquiv M e₂) := by ext; simp

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv_trans := mapRingEquiv_trans

/-- Nested monoid algebras can be taken in an arbitrary order. -/
@[to_additive (dont_translate := R)
/-- Nested additive monoid algebras can be taken in an arbitrary order. -/]
/-
**MonoidAlgebra.commRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：commRingEquiv : R[M][N] ≃+* R[N][M]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def commRingEquiv : R[M][N] ≃+* R[N][M] :=
  curryRingEquiv.symm.trans <| .trans (mapDomainRingEquiv _ <| .prodComm ..) curryRingEquiv

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.symm_commRingEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：symm_commRingEquiv : (commRingEquiv : R[M][N] ≃+* R[N][M]).symm = commRing
Equiv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_commRingEquiv : (commRingEquiv : R[M][N] ≃+* R[N][M]).symm = commRingEquiv := rfl

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.commRingEquiv_single_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlg
ebra`。
形式化陈述：commRingEquiv_single_single (m : M) (n : N) (r : R) : commRingEquiv (singl
e m <| single n r) = single n (single m r)
参数：m : M；n : N；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.curryRingEquiv_symm_single`：curryRingEquiv_symm_single (m 
: M) (n : N) (r : R) : curryRingEquiv.symm (single m <| single n r) = (single (m
, n) r)
· 使用引理 `MonoidAlgebra.mapDomainRingEquiv_single`：mapDomainRingEquiv_single (e : 
M ≃* N) (r : R) (m : M) : mapDomainRingEquiv R e (single m r) = single (e m) r
· 使用引理 `MonoidAlgebra.curryRingEquiv_single`：curryRingEquiv_single (m : M) (n : 
N) (r : R) : curryRingEquiv (single (m, n) r) = single m (single n r)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma commRingEquiv_single_single (m : M) (n : N) (r : R) :
    commRingEquiv (single m <| single n r) = single n (single m r) := by simp [commRingEquiv]

@[to_additive (dont_translate := R) (attr := simp)]
/-
**MonoidAlgebra.commRingEquiv_single_one** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebr
a`。
形式化陈述：commRingEquiv_single_one (m : M) : commRingEquiv (single m (1 : R[N])) = s
ingle 1 (single m 1)
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.commRingEquiv_single_single`：commRingEquiv_single_single (
m : M) (n : N) (r : R) : commRingEquiv (single m <| single n r) = single n (sing
le m r)
-/
lemma commRingEquiv_single_one (m : M) :
    commRingEquiv (single m (1 : R[N])) = single 1 (single m 1) := commRingEquiv_single_single ..

-- We want this to have higher priority than `commRingEquiv_single_single`
@[to_additive (dont_translate := R) (attr := simp high)]
/-
**MonoidAlgebra.commRingEquiv_single_one_single** 是 Mathlib 中的一个引理，位于命名空间 `Monoi
dAlgebra`。
形式化陈述：commRingEquiv_single_one_single (m : M) : commRingEquiv (single 1 <| singl
e m 1) = (single m (1 : R[N]))
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.commRingEquiv_single_single`：commRingEquiv_single_single (
m : M) (n : N) (r : R) : commRingEquiv (single m <| single n r) = single n (sing
le m r)
-/
lemma commRingEquiv_single_one_single (m : M) :
    commRingEquiv (single 1 <| single m 1) = (single m (1 : R[N])) := commRingEquiv_single_single ..

end Semiring

section Ring
variable [Ring R] [Ring S]

@[to_additive]
/-
**MonoidAlgebra.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：∀ {R : Type u_3} {S : Type u_4} {M : Type u_6} [inst : Ring R] [inst_1 : R
ing S] (f : R →+ S) (x : MonoidAlgebra R M),   MonoidAlgebra.map f (-x) = -Monoi
dAlgebra.map f x
参数：f : R →+ S；x : MonoidAlgebra R M；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma map_neg (f : R →+ S) (x : R[M]) : map f (-x) = -map f x := by ext; simp

@[to_additive]
/-
**MonoidAlgebra.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：∀ {R : Type u_3} {S : Type u_4} {M : Type u_6} [inst : Ring R] [inst_1 : R
ing S] (f : R →+ S) (x y : MonoidAlgebra R M),   MonoidAlgebra.map f (x - y) = M
onoidAlgebra.map f x - MonoidAlgebra.map f y
参数：f : R →+ S；x y : MonoidAlgebra R M；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma map_sub (f : R →+ S) (x y : R[M]) : map f (x - y) = map f x - map f y := by
  ext; simp

end Ring
end MonoidAlgebra

/-!
#### Conversions between `AddMonoidAlgebra` and `MonoidAlgebra`
-/

namespace AddMonoidAlgebra
variable [Semiring R] [Add M]

set_option backward.isDefEq.respectTransparency false in
variable (R M) in
/-- The equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms of
`Multiplicative` -/
@[simps]
/-
**AddMonoidAlgebra.toMultiplicative** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidAlgebra`
。
形式化陈述：toMultiplicative : AddMonoidAlgebra R M ≃+* MonoidAlgebra R (Multiplicativ
e M) where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms of
`Multiplicative`
-/
def toMultiplicative : AddMonoidAlgebra R M ≃+* MonoidAlgebra R (Multiplicative M) where
  toFun x := .ofCoeff <| x.coeff.mapDomain .ofAdd
  invFun x := .ofCoeff <| x.coeff.mapDomain Multiplicative.toAdd
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by simp [Finsupp.mapDomain_add]
  map_mul' x y := by
    classical
    ext
    simp [MonoidAlgebra.coeff_mul, coeff_mul, sum_mapDomain_index, add_mul, mul_add, ite_add_zero,
      Multiplicative.ext_iff]

@[simp]
/-
**AddMonoidAlgebra.toMultiplicative_single** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidA
lgebra`。
形式化陈述：toMultiplicative_single (m : M) (r : R) : toMultiplicative R M (single m r
) = .single (.ofAdd m) r
参数：m : M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toMultiplicative_single (m : M) (r : R) :
    toMultiplicative R M (single m r) = .single (.ofAdd m) r := by simp [toMultiplicative]

end AddMonoidAlgebra

namespace MonoidAlgebra
variable [Semiring R] [Mul M]

set_option backward.isDefEq.respectTransparency false in
variable (R M) in
/-- The equivalence between `MonoidAlgebra` and `AddMonoidAlgebra` in terms of `Additive` -/
@[simps]
/-
**MonoidAlgebra.toAdditive** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：toAdditive : MonoidAlgebra R M ≃+* AddMonoidAlgebra R (Additive M) where t
oFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `MonoidAlgebra` and `AddMonoidAlgebra` in terms of `Addi
tive`
-/
def toAdditive : MonoidAlgebra R M ≃+* AddMonoidAlgebra R (Additive M) where
  toFun x := .ofCoeff <| x.coeff.mapDomain .ofMul
  invFun x := .ofCoeff <| x.coeff.mapDomain Additive.toMul
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by simp [Finsupp.mapDomain_add]
  map_mul' x y := by
    classical
    ext
    simp [coeff_mul, AddMonoidAlgebra.coeff_mul, sum_mapDomain_index, add_mul, mul_add,
      ite_add_zero, Additive.ext_iff]

@[simp]
/-
**MonoidAlgebra.toAdditive_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：toAdditive_single (m : M) (r : R) : toAdditive R M (single m r) = .single 
(.ofMul m) r
参数：m : M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.coeff_toAdditive_apply`：∀ (R : Type u_3) (M : Type u_6) [i
nst : Semiring R] [inst_1 : Mul M] (x : MonoidAlgebra R M),   ((MonoidAlgebra.to
Additive R M) x).coeff = F…
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toAdditive_single (m : M) (r : R) : toAdditive R M (single m r) = .single (.ofMul m) r := by
  ext; simp

end MonoidAlgebra

