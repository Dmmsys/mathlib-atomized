/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Mathlib.Topology.Category.Profinite.Nobeling.Basic

/-!
# The good products span

Most of the argument is developing an API for `π C (· ∈ s)` when `s : Finset I`; then the image
of `C` is finite with the discrete topology. In this case, there is a direct argument that the good
products span. The general result is deduced from this.

For the overall proof outline see `Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean`.

## Main theorems

* `GoodProducts.spanFin` : The good products span the locally constant functions on `π C (· ∈ s)`
  if `s` is finite.
* `GoodProducts.span` : The good products span `LocallyConstant C ℤ` for every closed subset `C`.

## References

- [scholze2019condensed], Theorem 5.4.
-/

@[expose] public section

universe u

namespace Profinite.NobelingProof

variable {I : Type u} (C : Set (I → Bool)) [LinearOrder I]

section Fin

variable (s : Finset I)

/-- The `ℤ`-linear map induced by precomposition of the projection `C → π C (· ∈ s)`. -/
noncomputable
/-
**Profinite.NobelingProof.** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.NobelingProof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def πJ : LocallyConstant (π C (· ∈ s)) ℤ →ₗ[ℤ] LocallyConstant C ℤ :=
  LocallyConstant.comapₗ ℤ ⟨_, (continuous_projRestrict C (· ∈ s))⟩
/-
**Profinite.NobelingProof.eval_eq_** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobeling
Proof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval_eq_πJ (l : Products I) (hl : l.isGood (π C (· ∈ s))) :
    l.eval C = πJ C s (l.eval (π C (· ∈ s))) := by
  ext f
  simp only [πJ, LocallyConstant.comapₗ]
  exact (congr_fun (Products.evalFacProp C (· ∈ s) (Products.prop_of_isGood C (· ∈ s) hl)) _).symm

/-- `π C (· ∈ s)` is finite for a finite set `s`. -/
noncomputable
/-
**Profinite.NobelingProof.** 是 Mathlib 中的一个实例，位于命名空间 `Profinite.NobelingProof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Fintype (π C (· ∈ s)) := by
  let f : π C (· ∈ s) → (s → Bool) := fun x j ↦ x.val j.val
  refine Fintype.ofInjective f ?_
  intro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩ h
  ext i
  by_cases hi : i ∈ s
  · exact congrFun h ⟨i, hi⟩
  · simp only [Proj, if_neg hi]

open scoped Classical in
/-- The Kronecker delta as a locally constant map from `π C (· ∈ s)` to `ℤ`. -/
noncomputable
/-
**Profinite.NobelingProof.spanFinBasis** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Nobe
lingProof`。
形式化陈述：spanFinBasis (x : π C (· in s)) : LocallyConstant (π C (· in s)) Int where
 toFun
参数：x : π C (· in s)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def spanFinBasis (x : π C (· ∈ s)) : LocallyConstant (π C (· ∈ s)) ℤ where
  toFun := fun y ↦ if y = x then 1 else 0
  isLocallyConstant :=
    haveI : DiscreteTopology (π C (· ∈ s)) := Finite.instDiscreteTopology
    IsLocallyConstant.of_discrete _
/-
**Profinite.NobelingProof.spanFinBasis.span** 是 Mathlib 中的一个定理，位于命名空间 `Profinite
.NobelingProof.spanFinBasis`。
形式化陈述：∀ {I : Type u} (C : Set (I → Bool)) [inst : LinearOrder I] (s : Finset I),
   ⊤ ≤ Submodule.span ℤ (Set.range (Profinite.NobelingProof.spanFinBasis C s))
参数：C : Set (I → Bool)；s : Finset I；Set.range (Profinite.NobelingProof.spanFinBas
is C s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mem_span_range_iff_exists_finsupp`：mem_span_range_iff_exists_fin
supp {v : α -> M} {x : M} : x in span R (range v) ↔ exists c : α ->₀ R, (c.sum f
un i a => a • v i) = x
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LocallyConstant.evalₗ_apply`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] (R : Type u_6) [inst_1 : Semiring R]   [inst_2 : AddCommMonoid 
Y] [inst_3 : _roo…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finsupp.sum_ite_eq`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [ins
t : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : DecidableEq α]   (f : α →₀ M) (
a : α) (…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem spanFinBasis.span : ⊤ ≤ Submodule.span ℤ (Set.range (spanFinBasis C s)) := by
  intro f _
  rw [Finsupp.mem_span_range_iff_exists_finsupp]
  use Finsupp.onFinset (Finset.univ) f.toFun (fun _ _ ↦ Finset.mem_univ _)
  ext x
  change LocallyConstant.evalₗ ℤ x _ = _
  simp only [zsmul_eq_mul, map_finsuppSum, LocallyConstant.evalₗ_apply,
    LocallyConstant.coe_mul, Pi.mul_apply, spanFinBasis, LocallyConstant.coe_mk, mul_ite, mul_one,
    mul_zero, Finsupp.sum_ite_eq, Finsupp.mem_support_iff, ne_eq, ite_not]
  split_ifs with h <;> [exact h.symm; rfl]

/--
A certain explicit list of locally constant maps. The theorem `factors_prod_eq_basis` shows that the
product of the elements in this list is the delta function `spanFinBasis C s x`.
-/
/-
**Profinite.NobelingProof.factors** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.NobelingP
roof`。
形式化陈述：factors (x : π C (· in s)) : List (LocallyConstant (π C (· in s)) Int)
参数：x : π C (· in s)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LE.total'`：∀ {α : Type u} [inst : LinearOrder α], Std.Total fun x1 x2 =>
 x2 ≤ x1

--- 原说明 ---
A certain explicit list of locally constant maps. The theorem `factors_prod_eq_b
asis` shows that the
product of the elements in this list is the delta function `spanFinBasis C s x`.
-/
def factors (x : π C (· ∈ s)) : List (LocallyConstant (π C (· ∈ s)) ℤ) :=
  List.map (fun i ↦ if x.val i = true then e (π C (· ∈ s)) i else (1 - (e (π C (· ∈ s)) i)))
    (s.sort (· ≥ ·))
/-
**Profinite.NobelingProof.list_prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.N
obelingProof`。
形式化陈述：list_prod_apply {I} (C : Set (I -> Bool)) (x : C) (l : List (LocallyConsta
nt C Int)) : l.prod x = (l.map (LocallyConstant.evalMonoidHom x)).prod
参数：C : Set (I -> Bool)；x : C；l : List (LocallyConstant C Int)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
· 使用定理 `LocallyConstant.evalMonoidHom_apply`：∀ {X : Type u_1} {Y : Type u_2} [in
st : TopologicalSpace X] [inst_1 : MulOneClass Y] (x : X)   (x_1 : LocallyConsta
nt X Y), (LocallyConstant…
-/
theorem list_prod_apply {I} (C : Set (I → Bool)) (x : C) (l : List (LocallyConstant C ℤ)) :
    l.prod x = (l.map (LocallyConstant.evalMonoidHom x)).prod := by
  rw [← map_list_prod (LocallyConstant.evalMonoidHom x) l, LocallyConstant.evalMonoidHom_apply]

set_option backward.defeqAttrib.useBackward true in
/-
**Profinite.NobelingProof.factors_prod_eq_basis_of_eq** 是 Mathlib 中的一个定理，位于命名空间 
`Profinite.NobelingProof`。
形式化陈述：factors_prod_eq_basis_of_eq {x y : (π C fun x => x in s)} (h : y = x) : (f
actors C s x).prod y = 1
参数：π C fun x => x in s；h : y = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.list_prod_apply`：list_prod_apply {I} (C : Set (I
 -> Bool)) (x : C) (l : List (LocallyConstant C Int)) : l.prod x = (l.map (Local
lyConstant.evalMonoidHom x)).…
· 使用定理 `List.prod_eq_one`：∀ {M : Type u_4} [inst : Monoid M] {l : List M}, (∀ x 
∈ l, x = 1) → l.prod = 1
· 使用定理 `LE.total'`：∀ {α : Type u} [inst : LinearOrder α], Std.Total fun x1 x2 =>
 x2 ≤ x1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Profinite.NobelingProof.e.eq_1`：∀ {I : Type u} (C : Set (I → Bool)) (i :
 I),   Profinite.NobelingProof.e C i = { toFun := fun f => if ↑f i = true then 1
 else 0, isLocallyCo…
· 使用定理 `LocallyConstant.coe_mk`：coe_mk (f : X -> Y) (h) : ⇑(⟨f, h⟩ : LocallyCons
tant X Y) = f
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LocallyConstant.sub_apply`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topol
ogicalSpace X] [inst_1 : Sub Y] (f g : LocallyConstant X Y) (x : X),   (f - g) x
 = f x - g x
· 使用定理 `LocallyConstant.isLocallyConstant`：∀ {X : Type u_5} {Y : Type u_6} [inst
 : TopologicalSpace X] (self : LocallyConstant X Y), IsLocallyConstant self.toFu
n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factors_prod_eq_basis_of_eq {x y : (π C fun x ↦ x ∈ s)} (h : y = x) :
    (factors C s x).prod y = 1 := by
  rw [list_prod_apply (π C (· ∈ s)) y _]
  apply List.prod_eq_one
  simp only [h, List.mem_map, LocallyConstant.evalMonoidHom, factors]
  rintro _ ⟨a, ⟨b, _, rfl⟩, rfl⟩
  dsimp
  split_ifs with hh
  · rw [e, LocallyConstant.coe_mk, if_pos hh]
  · rw [LocallyConstant.sub_apply, e, LocallyConstant.coe_mk, LocallyConstant.coe_mk, if_neg hh]
    simp only [LocallyConstant.toFun_eq_coe, LocallyConstant.coe_one, Pi.one_apply, sub_zero]
/-
**Profinite.NobelingProof.e_mem_of_eq_true** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.
NobelingProof`。
形式化陈述：e_mem_of_eq_true {x : (π C (· in s))} {a : I} (hx : x.val a = true) : e (π
 C (· in s)) a in factors C s x
参数：π C (· in s)；hx : x.val a = true。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.total'`：∀ {α : Type u} [inst : LinearOrder α], Std.Total fun x1 x2 =>
 x2 ≤ x1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Bool.if_false_right`：∀ (p : Prop) [h : Decidable p] (t : Bool), (if p th
en t else false) = (decide p && t)
· 使用定理 `Bool.and_eq_true`：∀ (a b : Bool), ((a && b) = true) = (a = true ∧ b = tr
ue)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem e_mem_of_eq_true {x : (π C (· ∈ s))} {a : I} (hx : x.val a = true) :
    e (π C (· ∈ s)) a ∈ factors C s x := by
  rcases x with ⟨_, z, hz, rfl⟩
  simp only [factors, List.mem_map, Finset.mem_sort]
  refine ⟨a, ?_, if_pos hx⟩
  aesop (add simp Proj)
/-
**Profinite.NobelingProof.one_sub_e_mem_of_false** 是 Mathlib 中的一个定理，位于命名空间 `Prof
inite.NobelingProof`。
形式化陈述：one_sub_e_mem_of_false {x y : (π C (· in s))} {a : I} (ha : y.val a = true
) (hx : x.val a = false) : 1 - e (π C (· in s)) a in factors C s x
参数：π C (· in s)；ha : y.val a = true；hx : x.val a = false。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.total'`：∀ {α : Type u} [inst : LinearOrder α], Std.Total fun x1 x2 =>
 x2 ≤ x1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Bool.if_false_right`：∀ (p : Prop) [h : Decidable p] (t : Bool), (if p th
en t else false) = (decide p && t)
· 使用定理 `Bool.and_eq_true`：∀ (a b : Bool), ((a && b) = true) = (a = true ∧ b = tr
ue)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem one_sub_e_mem_of_false {x y : (π C (· ∈ s))} {a : I} (ha : y.val a = true)
    (hx : x.val a = false) : 1 - e (π C (· ∈ s)) a ∈ factors C s x := by
  simp only [factors, List.mem_map, Finset.mem_sort]
  use a
  simp only [hx]
  rcases y with ⟨_, z, hz, rfl⟩
  aesop (add simp Proj)
/-
**Profinite.NobelingProof.factors_prod_eq_basis_of_ne** 是 Mathlib 中的一个定理，位于命名空间 
`Profinite.NobelingProof`。
形式化陈述：factors_prod_eq_basis_of_ne {x y : (π C (· in s))} (h : y != x) : (factors
 C s x).prod y = 0
参数：π C (· in s)；h : y != x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.list_prod_apply`：list_prod_apply {I} (C : Set (I
 -> Bool)) (x : C) (l : List (LocallyConstant C Int)) : l.prod x = (l.map (Local
lyConstant.evalMonoidHom x)).…
· 使用定理 `List.prod_eq_zero`：∀ {M₀ : Type u_4} [inst : MonoidWithZero M₀] {l : Lis
t M₀}, 0 ∈ l → l.prod = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Profinite.NobelingProof.one_sub_e_mem_of_false`：one_sub_e_mem_of_false {
x y : (π C (· in s))} {a : I} (ha : y.val a = true) (hx : x.val a = false) : 1 -
 e (π C (· in s)) a in factors C s x
· 使用定理 `Bool.not_eq_false`：∀ (b : Bool), (¬b = false) = (b = true)
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Profinite.NobelingProof.e.eq_1`：∀ {I : Type u} (C : Set (I → Bool)) (i :
 I),   Profinite.NobelingProof.e C i = { toFun := fun f => if ↑f i = true then 1
 else 0, isLocallyCo…
· 使用定理 `LocallyConstant.evalMonoidHom_apply`：∀ {X : Type u_1} {Y : Type u_2} [in
st : TopologicalSpace X] [inst_1 : MulOneClass Y] (x : X)   (x_1 : LocallyConsta
nt X Y), (LocallyConstant…
· 使用定理 `LocallyConstant.sub_apply`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topol
ogicalSpace X] [inst_1 : Sub Y] (f g : LocallyConstant X Y) (x : X),   (f - g) x
 = f x - g x
· 使用定理 `LocallyConstant.coe_one`：coe_one [One Y] : ⇑(1 : LocallyConstant X Y) = 
(1 : X -> Y)
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1
· 使用定理 `LocallyConstant.coe_mk`：coe_mk (f : X -> Y) (h) : ⇑(⟨f, h⟩ : LocallyCons
tant X Y) = f
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Profinite.NobelingProof.e_mem_of_eq_true`：e_mem_of_eq_true {x : (π C (· 
in s))} {a : I} (hx : x.val a = true) : e (π C (· in s)) a in factors C s x
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem factors_prod_eq_basis_of_ne {x y : (π C (· ∈ s))} (h : y ≠ x) :
    (factors C s x).prod y = 0 := by
  rw [list_prod_apply (π C (· ∈ s)) y _]
  apply List.prod_eq_zero
  simp only [List.mem_map]
  obtain ⟨a, ha⟩ : ∃ a, y.val a ≠ x.val a := by contrapose! h; ext; apply h
  cases hx : x.val a
  · rw [hx, ne_eq, Bool.not_eq_false] at ha
    refine ⟨1 - (e (π C (· ∈ s)) a), ⟨one_sub_e_mem_of_false _ _ ha hx, ?_⟩⟩
    rw [e, LocallyConstant.evalMonoidHom_apply, LocallyConstant.sub_apply,
      LocallyConstant.coe_one, Pi.one_apply, LocallyConstant.coe_mk, if_pos ha, sub_self]
  · refine ⟨e (π C (· ∈ s)) a, ⟨e_mem_of_eq_true _ _ hx, ?_⟩⟩
    rw [hx] at ha
    rw [LocallyConstant.evalMonoidHom_apply, e, LocallyConstant.coe_mk, if_neg ha]

/-- If `s` is finite, the product of the elements of the list `factors C s x`
is the delta function at `x`. -/
/-
**Profinite.NobelingProof.factors_prod_eq_basis** 是 Mathlib 中的一个定理，位于命名空间 `Profi
nite.NobelingProof`。
形式化陈述：factors_prod_eq_basis (x : π C (· in s)) : (factors C s x).prod = spanFinB
asis C s x
参数：x : π C (· in s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Profinite.NobelingProof.factors_prod_eq_basis_of_eq`：factors_prod_eq_bas
is_of_eq {x y : (π C fun x => x in s)} (h : y = x) : (factors C s x).prod y = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Profinite.NobelingProof.factors_prod_eq_basis_of_ne`：factors_prod_eq_bas
is_of_ne {x y : (π C (· in s))} (h : y != x) : (factors C s x).prod y = 0

--- 原说明 ---
If `s` is finite, the product of the elements of the list `factors C s x`
is the delta function at `x`.
-/
theorem factors_prod_eq_basis (x : π C (· ∈ s)) :
    (factors C s x).prod = spanFinBasis C s x := by
  ext y
  dsimp [spanFinBasis]
  split_ifs with h <;> [exact factors_prod_eq_basis_of_eq _ _ h;
    exact factors_prod_eq_basis_of_ne _ _ h]
/-
**Profinite.NobelingProof.GoodProducts.finsuppSum_mem_span_eval** 是 Mathlib 中的一个
定理，位于命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：∀ {I : Type u} (C : Set (I → Bool)) [inst : LinearOrder I] (s : Finset I) 
{a : I} {as : List I},   List.IsChain (fun x1 x2 => x1 > x2) (a :: as) →     ∀ {
c : Profinite.NobelingProof.Products I →₀ ℤ},       ↑c.support ⊆ {m | ↑m ≤ as} →
         (c.sum fun a_1 b =>             Profinite.NobelingProof.e (Profinite.No
belingProof.π C fun x => x ∈ s) a *               b • Profinite.NobelingProof.Pr
oducts.eval (Profinite.NobelingProof.π C fun x => x ∈ s) a_1) ∈           Submod
ule.span ℤ             (Profinite.NobelingProof.Products.eval (Profinite.Nobelin
gProof.π C fun x => x ∈ s) '' {m | ↑m ≤ a :: as})
参数：C : Set (I → Bool)；s : Finset I；fun x1 x2 => x1 > x2；a :: as；c.sum fun a_1 b 
=>             Profinite.NobelingProof.e (Profinite.NobelingProof.π C fun x => x
 ∈ s) a *               b • Profinite.NobelingProof.Products.eval (Profinite.Nob
elingProof.π C fun x => x ∈ s) a_1；Profinite.NobelingProof.Products.eval (Profin
ite.NobelingProof.π C fun x => x ∈ s) '' {m | ↑m ≤ a :: as}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.finsuppSum_mem`：∀ (R : Type u_1) {M : Type u_2} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {ι : Type u_4} {
β : Type u_5} …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.IsChain.cons_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a : α}
 {as m : List α},   List.IsChain (fun x1 x2 => x1 > x2) (a :: as) →     List.IsC
hain (fun x1 …
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `List.cons_le_cons`：cons_le_cons [LinearOrder α] (a : α) {l l' : List α} 
(h : l' <= l) : a :: l' <= a :: l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem GoodProducts.finsuppSum_mem_span_eval {a : I} {as : List I}
    (ha : List.IsChain (· > ·) (a :: as)) {c : Products I →₀ ℤ}
    (hc : (c.support : Set (Products I)) ⊆ {m | m.val ≤ as}) :
    (Finsupp.sum c fun a_1 b ↦ e (π C (· ∈ s)) a * b • Products.eval (π C (· ∈ s)) a_1) ∈
      Submodule.span ℤ (Products.eval (π C (· ∈ s)) '' {m | m.val ≤ a :: as}) := by
  apply Submodule.finsuppSum_mem
  intro m hm
  have hsm := (LinearMap.mulLeft ℤ (e (π C (· ∈ s)) a)).map_smul
  dsimp at hsm
  rw [hsm]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  have hmas : m.val ≤ as := by
    apply hc
    simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hm
  refine ⟨⟨a :: m.val, ha.cons_of_le m.prop hmas⟩, ⟨List.cons_le_cons a hmas, ?_⟩⟩
  simp only [Products.eval, List.map, List.prod_cons]

/-- If `s` is a finite subset of `I`, then the good products span. -/
/-
**Profinite.NobelingProof.GoodProducts.spanFin** 是 Mathlib 中的一个定理，位于命名空间 `Profin
ite.NobelingProof.GoodProducts`。
形式化陈述：∀ {I : Type u} (C : Set (I → Bool)) [inst : LinearOrder I] (s : Finset I) 
[WellFoundedLT I],   ⊤ ≤     Submodule.span ℤ       (Set.range (Profinite.Nobeli
ngProof.GoodProducts.eval (Profinite.NobelingProof.π C fun x => x ∈ s)))
参数：C : Set (I → Bool)；s : Finset I；Set.range (Profinite.NobelingProof.GoodProduc
ts.eval (Profinite.NobelingProof.π C fun x => x ∈ s))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.GoodProducts.span_iff_products`：∀ {I : Type u} (
C : Set (I → Bool)) [inst : LinearOrder I] [WellFoundedLT I],   ⊤ ≤ Submodule.sp
an ℤ (Set.range (Profinite.NobelingProof.Goo…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Profinite.NobelingProof.spanFinBasis.span`：∀ {I : Type u} (C : Set (I → 
Bool)) [inst : LinearOrder I] (s : Finset I),   ⊤ ≤ Submodule.span ℤ (Set.range 
(Profinite.NobelingProof.spanFi…
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Profinite.NobelingProof.factors_prod_eq_basis`：factors_prod_eq_basis (x 
: π C (· in s)) : (factors C s x).prod = spanFinBasis C s x
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1
· 使用定理 `instAntisymmGe`：∀ {α : Type u} [inst : PartialOrder α], Std.Antisymm fun
 x1 x2 => x2 ≤ x1
· 使用定理 `LE.total'`：∀ {α : Type u} [inst : LinearOrder α], Std.Total fun x1 x2 =>
 x2 ≤ x1
· 使用定理 `List.sortedGT_iff_isChain`：sortedGT_iff_isChain : l.SortedGT ↔ IsChain (
· > ·) l
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `List.isChain_nil`：isChain_nil : IsChain R []
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.mem_span_image_iff_linearCombination`：mem_span_image_iff_linearC
ombination {s : Set α} {x : M} : x in span R (v '' s) ↔ exists l in supported R 
R s, linearCombination R v l = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.isChain_cons`：isChain_cons {x l} : IsChain R (x :: l) ↔ (forall y i
n head? l, R x y) ∧ IsChain R l
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Profinite.NobelingProof.GoodProducts.finsuppSum_mem_span_eval`：∀ {I : Ty
pe u} (C : Set (I → Bool)) [inst : LinearOrder I] (s : Finset I) {a : I} {as : L
ist I},   List.IsChain (fun x1 x2 => x1 > x2) (a ::…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
If `s` is a finite subset of `I`, then the good products span.
-/
theorem GoodProducts.spanFin [WellFoundedLT I] :
    ⊤ ≤ Submodule.span ℤ (Set.range (eval (π C (· ∈ s)))) := by
  rw [span_iff_products]
  refine le_trans (spanFinBasis.span C s) ?_
  rw [Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [← factors_prod_eq_basis]
  let l := s.sort (· ≥ ·)
  dsimp [factors]
  suffices l.SortedGT → (l.map (fun i ↦ if x.val i = true then e (π C (· ∈ s)) i
      else (1 - (e (π C (· ∈ s)) i)))).prod ∈
      Submodule.span ℤ ((Products.eval (π C (· ∈ s))) '' {m | m.val ≤ l}) from
    Submodule.span_mono (Set.image_subset_range _ _)
      (this (Finset.sortedGT_sort _))
  rw [List.sortedGT_iff_isChain]
  induction l with
  | nil =>
    intro _
    apply Submodule.subset_span
    exact ⟨⟨[], List.isChain_nil⟩,⟨Or.inl rfl, rfl⟩⟩
  | cons a as ih =>
    rw [List.map_cons, List.prod_cons]
    intro ha
    specialize ih (by rw [List.isChain_cons] at ha; exact ha.2)
    rw [Finsupp.mem_span_image_iff_linearCombination] at ih
    simp only [Finsupp.mem_supported, Finsupp.linearCombination_apply] at ih
    obtain ⟨c, hc, hc'⟩ := ih
    rw [← hc']; clear hc'
    have hmap := fun g ↦ map_finsuppSum (LinearMap.mulLeft ℤ (e (π C (· ∈ s)) a)) c g
    dsimp at hmap ⊢
    split_ifs
    · rw [hmap]
      exact finsuppSum_mem_span_eval _ _ ha hc
    · noncomm_ring
      -- we use `noncomm_ring` even though this is a commutative ring, because we want a weaker
      -- normalization which preserves multiplication order (i.e. doesn't use commutativity rules)
      rw [hmap]
      apply Submodule.add_mem
      · apply Submodule.finsuppSum_mem
        intro m hm
        apply Submodule.smul_mem
        apply Submodule.subset_span
        refine ⟨m, ⟨?_, rfl⟩⟩
        simp only [Set.mem_ofPred_eq]
        have hmas : m.val ≤ as :=
          hc (by simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hm)
        refine le_trans hmas ?_
        cases as with
        | nil => exact (List.nil_lt_cons a []).le
        | cons b bs =>
          apply le_of_lt
          rw [List.isChain_cons_cons] at ha
          exact (List.lt_iff_lex_lt _ _).mp (List.Lex.rel ha.1)
      · apply Submodule.smul_mem
        exact finsuppSum_mem_span_eval _ _ ha hc

end Fin

/-
**Profinite.NobelingProof.fin_comap_jointlySurjective** 是 Mathlib 中的一个定理，位于命名空间 
`Profinite.NobelingProof`。
形式化陈述：fin_comap_jointlySurjective (hC : IsClosed C) (f : LocallyConstant C Int) 
: exists (s : Finset I) (g : LocallyConstant (π C (· in s)) Int), f = g.comap ⟨(
ProjRestrict C (· in s)), continuous_projRestrict _ _⟩
参数：hC : IsClosed C；f : LocallyConstant C Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `Finite.compactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Finite 
X], CompactSpace X
· 使用定理 `Profinite.NobelingProof.continuous_projRestrict`：continuous_projRestrict
 : Continuous (ProjRestrict C J)
· 使用定理 `Profinite.exists_locallyConstant`：exists_locallyConstant {α : Type*} (hC
 : IsLimit C) (f : LocallyConstant C.pt α) : exists (j : J) (g : LocallyConstant
 (F.obj j) α), f = g.c…
· 使用定理 `CategoryTheory.isFiltered_of_directed_le_nonempty`：∀ (α : Type u) [inst 
: Preorder α] [IsDirectedOrder α] [Nonempty α], CategoryTheory.IsFiltered α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem fin_comap_jointlySurjective
    (hC : IsClosed C)
    (f : LocallyConstant C ℤ) : ∃ (s : Finset I)
    (g : LocallyConstant (π C (· ∈ s)) ℤ), f = g.comap ⟨(ProjRestrict C (· ∈ s)),
      continuous_projRestrict _ _⟩ := by
  obtain ⟨J, g, h⟩ := @Profinite.exists_locallyConstant (Finset I)ᵒᵖ _ _ _
    (spanCone hC.isCompact) ℤ
    (spanCone_isLimit hC.isCompact) f
  exact ⟨(Opposite.unop J), g, h⟩

/-- The good products span all of `LocallyConstant C ℤ` if `C` is closed. -/
/-
**Profinite.NobelingProof.GoodProducts.span** 是 Mathlib 中的一个定理，位于命名空间 `Profinite
.NobelingProof.GoodProducts`。
形式化陈述：∀ {I : Type u} (C : Set (I → Bool)) [inst : LinearOrder I] [WellFoundedLT 
I],   IsClosed C → ⊤ ≤ Submodule.span ℤ (Set.range (Profinite.NobelingProof.Good
Products.eval C))
参数：C : Set (I → Bool)；Set.range (Profinite.NobelingProof.GoodProducts.eval C)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.GoodProducts.span_iff_products`：∀ {I : Type u} (
C : Set (I → Bool)) [inst : LinearOrder I] [WellFoundedLT I],   ⊤ ≤ Submodule.sp
an ℤ (Set.range (Profinite.NobelingProof.Goo…
· 使用定理 `Profinite.NobelingProof.fin_comap_jointlySurjective`：fin_comap_jointlySu
rjective (hC : IsClosed C) (f : LocallyConstant C Int) : exists (s : Finset I) (
g : LocallyConstant (π C (· in s)) Int), …
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Profinite.NobelingProof.eval_eq_πJ`：eval_eq_πJ (l : Products I) (hl : l.
isGood (π C (· in s))) : l.eval C = πJ C s (l.eval (π C (· in s)))
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Submodule.apply_mem_span_image_of_mem_span`：apply_mem_span_image_of_mem_
span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) {x : M} {s : Set M} (h : x in 
Submodule.span R s) : f x in Sub…
· 使用定理 `Profinite.NobelingProof.GoodProducts.spanFin`：∀ {I : Type u} (C : Set (I
 → Bool)) [inst : LinearOrder I] (s : Finset I) [WellFoundedLT I],   ⊤ ≤     Sub
module.span ℤ       (Set.range (Pr…
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The good products span all of `LocallyConstant C ℤ` if `C` is closed.
-/
theorem GoodProducts.span [WellFoundedLT I] (hC : IsClosed C) :
    ⊤ ≤ Submodule.span ℤ (Set.range (eval C)) := by
  rw [span_iff_products]
  intro f _
  obtain ⟨K, f', rfl⟩ : ∃ K f', f = πJ C K f' := fin_comap_jointlySurjective C hC f
  refine Submodule.span_mono ?_ <| Submodule.apply_mem_span_image_of_mem_span (πJ C K) <|
    spanFin C K (Submodule.mem_top : f' ∈ ⊤)
  rintro l ⟨y, ⟨m, rfl⟩, rfl⟩
  exact ⟨m.val, eval_eq_πJ C K m.val m.prop⟩

end Profinite.NobelingProof

