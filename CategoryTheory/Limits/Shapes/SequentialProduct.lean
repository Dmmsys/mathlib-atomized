/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.PiProd
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.CategoryTheory.EffectiveEpi.Basic
/-!

# ℕ-indexed products as sequential limits

Given sequences `M N : ℕ → C` of objects with morphisms `f n : M n ⟶ N n` for all `n`, this file
exhibits `∏ M` as the limit of the tower

```
⋯ → ∏_{n < m + 1} M n × ∏_{n ≥ m + 1} N n → ∏_{n < m} M n × ∏_{n ≥ m} N n → ⋯ → ∏ N
```

Further, we prove that the transition maps in this tower are epimorphisms, in the case when each
`f n` is an epimorphism and `C` has finite biproducts.
-/

@[expose] public section

namespace CategoryTheory.Limits.SequentialProduct

variable {C : Type*} {M N : ℕ → C}

/-
**CategoryTheory.Limits.SequentialProduct.functorObj_eq_pos** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits.SequentialProduct`。
形式化陈述：functorObj_eq_pos {n m : Nat} (h : m < n) : (fun i => if _ : i < n then M 
i else N i) m = M m
参数：h : m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma functorObj_eq_pos {n m : ℕ} (h : m < n) :
    (fun i ↦ if _ : i < n then M i else N i) m = M m := dif_pos h
/-
**CategoryTheory.Limits.SequentialProduct.functorObj_eq_neg** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits.SequentialProduct`。
形式化陈述：functorObj_eq_neg {n m : Nat} (h : ¬(m < n)) : (fun i => if _ : i < n then
 M i else N i) m = N m
参数：h : ¬(m < n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma functorObj_eq_neg {n m : ℕ} (h : ¬(m < n)) :
    (fun i ↦ if _ : i < n then M i else N i) m = N m := dif_neg h

variable [Category* C] (f : ∀ n, M n ⟶ N n) [HasCountableProducts C]

variable (M N) in
/-- The product of the `m` first objects of `M` and the rest of the rest of `N` -/
/-
**CategoryTheory.Limits.SequentialProduct.functorObj** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.SequentialProduct`。
形式化陈述：functorObj : Nat -> C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of the `m` first objects of `M` and the rest of the rest of `N`
-/
noncomputable def functorObj : ℕ → C :=
  fun n ↦ ∏ᶜ (fun m ↦ if _ : m < n then M m else N m)

/-- The projection map from `functorObj M N n` to `M m`, when `m < n` -/
/-
**CategoryTheory.Limits.SequentialProduct.functorObjProj_pos** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Limits.SequentialProduct`。
形式化陈述：functorObjProj_pos (n m : Nat) (h : m < n) : functorObj M N n ⟶ M m
参数：n m : Nat；h : m < n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection map from `functorObj M N n` to `M m`, when `m < n`
-/
noncomputable def functorObjProj_pos (n m : ℕ) (h : m < n) :
    functorObj M N n ⟶ M m :=
  Pi.π (fun m ↦ if _ : m < n then M m else N m) m ≫ eqToHom (functorObj_eq_pos (by lia))

/-- The projection map from `functorObj M N n` to `N m`, when `m ≥ n` -/
/-
**CategoryTheory.Limits.SequentialProduct.functorObjProj_neg** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Limits.SequentialProduct`。
形式化陈述：functorObjProj_neg (n m : Nat) (h : ¬(m < n)) : functorObj M N n ⟶ N m
参数：n m : Nat；h : ¬(m < n)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection map from `functorObj M N n` to `N m`, when `m ≥ n`
-/
noncomputable def functorObjProj_neg (n m : ℕ) (h : ¬(m < n)) :
    functorObj M N n ⟶ N m :=
  Pi.π (fun m ↦ if _ : m < n then M m else N m) m ≫ eqToHom (functorObj_eq_neg (by lia))

/-- The transition maps in the sequential limit of products -/
/-
**CategoryTheory.Limits.SequentialProduct.functorMap** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.SequentialProduct`。
形式化陈述：functorMap : forall n, functorObj M N (n + 1) ⟶ functorObj M N n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transition maps in the sequential limit of products
-/
noncomputable def functorMap : ∀ n,
    functorObj M N (n + 1) ⟶ functorObj M N n := by
  intro n
  refine Limits.Pi.map fun m ↦ if h : m < n then eqToHom ?_ else
    if h' : m < n + 1 then eqToHom ?_ ≫ f m ≫ eqToHom ?_ else eqToHom ?_
  all_goals split_ifs; try rfl; try lia

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.SequentialProduct.functorMap_commSq_succ** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Limits.SequentialProduct`。
形式化陈述：functorMap_commSq_succ (n : Nat) : (Functor.ofOpSequence (functorMap f)).m
ap (homOfLE (by lia : n <= n + 1)).op ≫ Pi.π _ n ≫ eqToHom (functorObj_eq_neg (b
y lia : ¬(n < n))) = (Pi.π (fun i => if _ : i < (n + 1) then M i else N i) n) ≫ 
eqToHom (functorObj_eq_pos (by lia)) ≫ f n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.Limits.SequentialProduct.functorObj_eq_neg`：functorObj_eq
_neg {n m : Nat} (h : ¬(m < n)) : (fun i => if _ : i < n then M i else N i) m = 
N m
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasProductsOfShapeOfHasCountableProductsOfCoun
table`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryT
heory.Limits.HasCountableProducts C]   (J : Type u_3) [Countable J]…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用引理 `CategoryTheory.Limits.SequentialProduct.functorObj_eq_pos`：functorObj_eq
_pos {n m : Nat} (h : m < n) : (fun i => if _ : i < n then M i else N i) m = M m
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用引理 `CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ`：ofOpSequence_map_h
omOfLE_succ (n : Nat) : (ofOpSequence f).map (homOfLE (Nat.le_add_right n 1)).op
 = f n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.Limits.Pi.map_π_assoc`：∀ {β : Type w} {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Lim
its.HasProduct f] [inst_2 …
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma functorMap_commSq_succ (n : ℕ) :
    (Functor.ofOpSequence (functorMap f)).map (homOfLE (by lia : n ≤ n + 1)).op ≫ Pi.π _ n ≫
      eqToHom (functorObj_eq_neg (by lia : ¬(n < n))) =
        (Pi.π (fun i ↦ if _ : i < (n + 1) then M i else N i) n) ≫
          eqToHom (functorObj_eq_pos (by lia)) ≫ f n := by
  simp [functorMap]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.SequentialProduct.functorMap_commSq_aux** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Limits.SequentialProduct`。
形式化陈述：functorMap_commSq_aux {n m k : Nat} (h : n <= m) (hh : ¬(k < m)) : (Functo
r.ofOpSequence (functorMap f)).map (homOfLE h).op ≫ Pi.π _ k ≫ eqToHom (functorO
bj_eq_neg (by lia : ¬(k < n))) = (Pi.π (fun i => if _ : i < m then M i else N i)
 k) ≫ eqToHom (functorObj_eq_neg hh)
参数：h : n <= m；hh : ¬(k < m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.SequentialProduct.functorObj_eq_neg`：functorObj_eq
_neg {n m : Nat} (h : ¬(m < n)) : (fun i => if _ : i < n then M i else N i) m = 
N m
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasProductsOfShapeOfHasCountableProductsOfCoun
table`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryT
heory.Limits.HasCountableProducts C]   (J : Type u_3) [Countable J]…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.le_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n ≤ m.succ
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用引理 `CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ`：ofOpSequence_map_h
omOfLE_succ (n : Nat) : (ofOpSequence f).map (homOfLE (Nat.le_add_right n 1)).op
 = f n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `CategoryTheory.Limits.Pi.map_π_assoc`：∀ {β : Type w} {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Lim
its.HasProduct f] [inst_2 …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
-/
lemma functorMap_commSq_aux {n m k : ℕ} (h : n ≤ m) (hh : ¬(k < m)) :
    (Functor.ofOpSequence (functorMap f)).map (homOfLE h).op ≫ Pi.π _ k ≫
      eqToHom (functorObj_eq_neg (by lia : ¬(k < n))) =
        (Pi.π (fun i ↦ if _ : i < m then M i else N i) k) ≫
          eqToHom (functorObj_eq_neg hh) := by
  induction h using Nat.leRec with
  | refl => simp
  | @le_succ_of_le m h ih =>
    specialize ih (by lia)
    have : homOfLE (by lia : n ≤ m + 1) =
        homOfLE (by lia : n ≤ m) ≫ homOfLE (by lia : m ≤ m + 1) := by simp
    rw [this, op_comp, Functor.map_comp]
    slice_lhs 2 4 => rw [ih]
    simp only [homOfLE_leOfHom, Functor.ofOpSequence_map_homOfLE_succ,
      functorMap, dite_eq_ite]
    split_ifs
    · omega
    simp [dif_neg (by lia : ¬(k < m)), dif_neg hh]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.SequentialProduct.functorMap_commSq** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits.SequentialProduct`。
形式化陈述：functorMap_commSq {n m : Nat} (h : ¬(m < n)) : (Functor.ofOpSequence (func
torMap f)).map (homOfLE (by lia : n <= m + 1)).op ≫ Pi.π _ m ≫ eqToHom (functorO
bj_eq_neg (by lia : ¬(m < n))) = (Pi.π (fun i => if _ : i < m + 1 then M i else 
N i) m) ≫ eqToHom (functorObj_eq_pos (by lia)) ≫ f m
参数：h : ¬(m < n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.SequentialProduct.functorObj_eq_neg`：functorObj_eq
_neg {n m : Nat} (h : ¬(m < n)) : (fun i => if _ : i < n then M i else N i) m = 
N m
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasProductsOfShapeOfHasCountableProductsOfCoun
table`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryT
heory.Limits.HasCountableProducts C]   (J : Type u_3) [Countable J]…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用引理 `CategoryTheory.Limits.SequentialProduct.functorObj_eq_pos`：functorObj_eq
_pos {n m : Nat} (h : m < n) : (fun i => if _ : i < n then M i else N i) m = M m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用引理 `CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ`：ofOpSequence_map_h
omOfLE_succ (n : Nat) : (ofOpSequence f).map (homOfLE (Nat.le_add_right n 1)).op
 = f n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.Pi.map_π`：∀ {β : Type w} {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] [inst_2 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Limits.SequentialProduct.functorMap_commSq_succ`：functorM
ap_commSq_succ (n : Nat) : (Functor.ofOpSequence (functorMap f)).map (homOfLE (b
y lia : n <= n + 1)).op ≫ Pi.π _ n ≫ eqToHom (functo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Limits.SequentialProduct.functorMap_commSq_aux`：functorMa
p_commSq_aux {n m k : Nat} (h : n <= m) (hh : ¬(k < m)) : (Functor.ofOpSequence 
(functorMap f)).map (homOfLE h).op ≫ Pi.π _ k ≫ eqT…
-/
lemma functorMap_commSq {n m : ℕ} (h : ¬(m < n)) :
    (Functor.ofOpSequence (functorMap f)).map (homOfLE (by lia : n ≤ m + 1)).op ≫ Pi.π _ m ≫
      eqToHom (functorObj_eq_neg (by lia : ¬(m < n))) =
        (Pi.π (fun i ↦ if _ : i < m + 1 then M i else N i) m) ≫
          eqToHom (functorObj_eq_pos (by lia)) ≫ f m := by
  cases m with
  | zero =>
      have : n = 0 := by lia
      subst this
      simp [functorMap]
  | succ m =>
      rw [← functorMap_commSq_succ f (m + 1)]
      simp only [homOfLE_leOfHom, dite_eq_ite,
        Functor.ofOpSequence_map_homOfLE_succ]
      have : homOfLE (by lia : n ≤ m + 1 + 1) =
          homOfLE (by lia : n ≤ m + 1) ≫ homOfLE (by lia : m + 1 ≤ m + 1 + 1) := by simp
      rw [this, op_comp, Functor.map_comp]
      simp only [homOfLE_leOfHom, Functor.ofOpSequence_map_homOfLE_succ,
        Category.assoc]
      congr 1
      exact functorMap_commSq_aux f (by lia) (by lia)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
The cone over the tower
```
⋯ → ∏_{n < m} M n × ∏_{n ≥ m} N n → ⋯ → ∏ N
```
with cone point `∏ M`. This is a limit cone, see `CategoryTheory.Limits.SequentialProduct.isLimit`.
-/
/-
**CategoryTheory.Limits.SequentialProduct.cone** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.SequentialProduct`。
形式化陈述：cone : Cone (Functor.ofOpSequence (functorMap f)) where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone over the tower
```
⋯ → ∏_{n < m} M n × ∏_{n ≥ m} N n → ⋯ → ∏ N
```
with cone point `∏ M`. This is a limit cone, see `CategoryTheory.Limits.Sequenti
alProduct.isLimit`.
-/
noncomputable def cone : Cone (Functor.ofOpSequence (functorMap f)) where
  pt := ∏ᶜ M
  π := by
    refine NatTrans.ofOpSequence
      (fun n ↦ Limits.Pi.map fun m ↦ if h : m < n then eqToHom (functorObj_eq_pos h).symm else
        f m ≫ eqToHom (functorObj_eq_neg h).symm) (fun n ↦ ?_)
    apply Limits.Pi.hom_ext
    intro m
    simp only [Functor.const_obj_obj, dite_eq_ite, Functor.ofOpSequence_obj, homOfLE_leOfHom,
      Functor.const_obj_map, Category.id_comp, Pi.map_π, Functor.ofOpSequence_map_homOfLE_succ,
      functorMap, Category.assoc, Pi.map_π_assoc]
    split
    · simp [dif_pos (by lia : m < n + 1)]
    · split
      all_goals simp
/-
**CategoryTheory.Limits.SequentialProduct.cone_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits.SequentialProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cone_π_app (n : ℕ) : (cone f).π.app ⟨n⟩ =
    Limits.Pi.map fun m ↦ if h : m < n then eqToHom (functorObj_eq_pos h).symm else
    f m ≫ eqToHom (functorObj_eq_neg h).symm := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.SequentialProduct.cone_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits.SequentialProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cone_π_app_comp_Pi_π_pos (m n : ℕ) (h : n < m) : (cone f).π.app ⟨m⟩ ≫
    Pi.π (fun i ↦ if _ : i < m then M i else N i) n =
    Pi.π _ n ≫ eqToHom (functorObj_eq_pos h).symm := by
  simp [cone_π_app, dif_pos h]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.SequentialProduct.cone_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits.SequentialProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cone_π_app_comp_Pi_π_neg (m n : ℕ) (h : ¬(n < m)) : (cone f).π.app ⟨m⟩ ≫ Pi.π _ n =
    Pi.π _ n ≫ f n ≫ eqToHom (functorObj_eq_neg h).symm := by
  simp [cone_π_app, dif_neg h]

set_option backward.isDefEq.respectTransparency false in
/--
The cone over the tower
```
⋯ → ∏_{n < m} M n × ∏_{n ≥ m} N n → ⋯ → ∏ N
```
with cone point `∏ M` is indeed a limit cone.
-/
/-
**CategoryTheory.Limits.SequentialProduct.isLimit** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.SequentialProduct`。
形式化陈述：isLimit : IsLimit (cone f) where lift s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone over the tower
```
⋯ → ∏_{n < m} M n × ∏_{n ≥ m} N n → ⋯ → ∏ N
```
with cone point `∏ M` is indeed a limit cone.
-/
noncomputable def isLimit : IsLimit (cone f) where
  lift s := Pi.lift fun m ↦
    s.π.app ⟨m + 1⟩ ≫ Pi.π (fun i ↦ if _ : i < m + 1 then M i else N i) m ≫
      eqToHom (dif_pos (by lia : m < m + 1))
  fac s := by
    intro ⟨n⟩
    apply Pi.hom_ext
    intro m
    by_cases h : m < n
    · simp only [Category.assoc, cone_π_app_comp_Pi_π_pos f _ _ h]
      simp only [dite_eq_ite, limit.lift_π_assoc,
        Discrete.functor_obj_eq_as, Fan.mk_π_app, Category.assoc, eqToHom_trans]
      have hh : m + 1 ≤ n := by lia
      rw [← s.w (homOfLE hh).op]
      simp only [homOfLE_leOfHom, Category.assoc]
      congr
      induction hh using Nat.leRec with
      | refl => simp
      | @le_succ_of_le n hh ih =>
        have : homOfLE (Nat.le_succ_of_le hh) = homOfLE hh ≫ homOfLE (Nat.le_succ n) := by simp
        rw [this, op_comp, Functor.map_comp]
        simp only [Nat.succ_eq_add_one, homOfLE_leOfHom,
          Functor.ofOpSequence_map_homOfLE_succ, Category.assoc]
        have h₁ : (if _ : m < m + 1 then M m else N m) = if _ : m < n then M m else N m := by
          rw [dif_pos (by lia), dif_pos (by lia)]
        have h₂ : (if _ : m < n then M m else N m) = if _ : m < n + 1 then M m else N m := by
          rw [dif_pos h, dif_pos (by lia)]
        rw [← eqToHom_trans h₁ h₂]
        slice_lhs 2 4 => rw [ih (by lia)]
        simp only [functorMap, dite_eq_ite, Pi.π, Pi.map_π_assoc]
        split_ifs
        rw [dif_pos (by lia)]
        simp
    · simp only [Category.assoc]
      rw [cone_π_app_comp_Pi_π_neg f _ _ h]
      simp only [dite_eq_ite, limit.lift_π_assoc,
        Discrete.functor_obj_eq_as, Fan.mk_π_app, Category.assoc]
      slice_lhs 2 4 => simp only [← dite_eq_ite, ← functorMap_commSq f h]
      simp
  uniq s m h := by
    apply Pi.hom_ext
    intro n
    simp only [dite_eq_ite, limit.lift_π,
      Fan.mk_π_app, ← h ⟨n + 1⟩, Category.assoc]
    slice_rhs 2 3 => simp only [← dite_eq_ite, cone_π_app_comp_Pi_π_pos f (n + 1) n (by lia)]
    simp

section

variable [HasZeroMorphisms C] [HasFiniteBiproducts C] [∀ n, Epi (f n)]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.SequentialProduct.functorMap_epi** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits.SequentialProduct`。
形式化陈述：functorMap_epi (n : Nat) : Epi (functorMap f n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.SequentialProduct.functorMap.eq_1`：∀ {C : Type u_1
} {M N : ℕ → C} [inst : CategoryTheory.Category.{v_1, u_1} C] (f : (n : ℕ) → M n
 ⟶ N n)   [inst_1 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Limits.hasProduct_of_hasBiproduct`：∀ {J : Type w} {C : Ty
pe uC} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C] {F : J → C} …
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `instFiniteSubtypeLtOfLocallyFiniteOrderBot`：∀ {α : Type u_1} [inst : Pre
order α] {y : α} [LocallyFiniteOrderBot α], Finite { x // x < y }
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasProductsOfShapeOfHasCountableProductsOfCoun
table`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryT
heory.Limits.HasCountableProducts C]   (J : Type u_3) [Countable J]…
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `instCountableNat`：Countable ℕ
· 使用引理 `CategoryTheory.Limits.hasBinaryProduct_of_products`：hasBinaryProduct_of_
products : HasBinaryProduct (∏ᶜ (fun (i : {x : I // P x}) => X i.val)) (∏ᶜ (fun 
(i : {x : I // ¬ P x}) => X i.val))
· 使用定理 `CategoryTheory.Limits.Pi.map_eq_prod_map`：∀ {C : Type u_1} {I : Type u_2
} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : I → C} (f : (i : I) → X i
 ⟶ Y i)   (P : I → Prop) [inst…
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.prod.map_epi`：∀ {C : Type uC} [inst : CategoryTheo
ry.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {
W X Y Z : C} (f : W ⟶ Y)…
· 使用定理 `CategoryTheory.Limits.Pi.map_epi`：∀ {J : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C] {f g : J → C} [i…
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.Limits.Pi.map_isIso`：∀ {β : Type w} {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limit
s.HasProductsOfShape β C…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts`：hasBinar
yBiproducts_of_finite_biproducts [HasFiniteBiproducts C] : HasBinaryBiproducts C
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma functorMap_epi (n : ℕ) : Epi (functorMap f n) := by
  rw [functorMap, Pi.map_eq_prod_map (P := fun m : ℕ ↦ m < n + 1)]
  apply +allowSynthFailures epi_comp
  apply +allowSynthFailures epi_comp
  apply +allowSynthFailures prod.map_epi
  · apply +allowSynthFailures Pi.map_epi
    intro ⟨_, _⟩
    split
    all_goals infer_instance
  · apply +allowSynthFailures IsIso.epi_of_iso
    apply +allowSynthFailures Pi.map_isIso
    intro ⟨_, _⟩
    split
    all_goals infer_instance
end

end CategoryTheory.Limits.SequentialProduct

