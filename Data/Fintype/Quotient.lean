/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yuyang Zhao
-/
module

public import Mathlib.Data.List.Pi
public import Mathlib.Data.Fintype.Defs

/-!
# Quotients of families indexed by a finite type

This file proves some basic facts and defines lifting and recursion principle for quotients indexed
by a finite type.

## Main definitions

* `Quotient.finChoice`: Given a function `f : Π i, Quotient (S i)` on a fintype `ι`, returns the
  class of functions `Π i, α i` sending each `i` to an element of the class `f i`.
* `Quotient.finChoiceEquiv`: A finite family of quotients is equivalent to a quotient of
  finite families.
* `Quotient.finLiftOn`: Given a fintype `ι`. A function on `Π i, α i` which respects
  setoid `S i` for each `i` can be lifted to a function on `Π i, Quotient (S i)`.
* `Quotient.finRecOn`: Recursion principle for quotients indexed by a finite type. It is the
  dependent version of `Quotient.finLiftOn`.

-/

@[expose] public section

-- We want the theorems in this file to be constructive.
set_option linter.unusedDecidableInType false

namespace Quotient

section List
variable {ι : Type*} [DecidableEq ι] {α : ι → Sort*} {S : ∀ i, Setoid (α i)} {β : Sort*}

/-- Given a collection of setoids indexed by a type `ι`, a list `l` of indices, and a function that
  for each `i ∈ l` gives a term of the corresponding quotient type, then there is a corresponding
  term in the quotient of the product of the setoids indexed by `l`. -/
/-
**Quotient.listChoice** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：listChoice {l : List ι} (q : forall i in l, Quotient (S i)) : @Quotient (f
orall i in l, α i) piSetoid
参数：q : forall i in l, Quotient (S i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a collection of setoids indexed by a type `ι`, a list `l` of indices, and 
a function that
  for each `i ∈ l` gives a term of the corresponding quotient type, then there i
s a corresponding
  term in the quotient of the product of the setoids indexed by `l`.
-/
def listChoice {l : List ι} (q : ∀ i ∈ l, Quotient (S i)) : @Quotient (∀ i ∈ l, α i) piSetoid :=
  match l with
  | [] => ⟦nofun⟧
  | i :: _ => Quotient.liftOn₂ (List.Pi.head (i := i) q)
    (listChoice (List.Pi.tail q))
    (⟦List.Pi.cons _ _ · ·⟧)
    (fun _ _ _ _ ha hl ↦ Quotient.sound (List.Pi.forall_rel_cons_ext ha hl))
/-
**Quotient.listChoice_mk** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：listChoice_mk {l : List ι} (a : forall i in l, α i) : listChoice (S
参数：a : forall i in l, α i。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem listChoice_mk {l : List ι} (a : ∀ i ∈ l, α i) : listChoice (S := S) (⟦a · ·⟧) = ⟦a⟧ :=
  match l with
  | [] => Quotient.sound nofun
  | i :: l => by
    unfold listChoice List.Pi.tail
    rw [listChoice_mk]
    exact congrArg (⟦·⟧) (List.Pi.cons_eta a)

/-- Choice-free induction principle for quotients indexed by a `List`. -/
@[elab_as_elim]
/-
**Quotient.list_ind** 是 Mathlib 中的一个引理，位于命名空间 `Quotient`。
形式化陈述：list_ind {l : List ι} {C : (forall i in l, Quotient (S i)) -> Prop} (f : f
orall a : forall i in l, α i, C (⟦a · ·⟧)) (q : forall i in l, Quotient (S i)) :
 C q
参数：forall i in l, Quotient (S i)；f : forall a : forall i in l, α i, C (⟦a · ·⟧)；
q : forall i in l, Quotient (S i)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Choice-free induction principle for quotients indexed by a `List`.
-/
lemma list_ind {l : List ι} {C : (∀ i ∈ l, Quotient (S i)) → Prop}
    (f : ∀ a : ∀ i ∈ l, α i, C (⟦a · ·⟧)) (q : ∀ i ∈ l, Quotient (S i)) : C q :=
  match l with
  | [] => cast (congr_arg _ (funext₂ nofun)) (f nofun)
  | i :: l => by
    rw [← List.Pi.cons_eta q]
    induction List.Pi.head q using Quotient.ind with | _ a
    refine @list_ind _ (fun q ↦ C (List.Pi.cons _ _ ⟦a⟧ q)) ?_ (List.Pi.tail q)
    intro as
    rw [List.Pi.cons_map a as (fun i ↦ Quotient.mk (S i))]
    exact f _

end List

section Fintype

-- `Fintype.ofFinite` depends on this file, so the `unusedFintypeInType` linter
-- makes no sense yet.
set_option linter.unusedFintypeInType false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Sort*} {S : ∀ i, Setoid (α i)} {β : Sort*}

/-- Choice-free induction principle for quotients indexed by a finite type.
  See `Quotient.induction_on_pi` for the general version assuming `Classical.choice`. -/
@[elab_as_elim]
/-
**Quotient.ind_fintype_pi** 是 Mathlib 中的一个引理，位于命名空间 `Quotient`。
形式化陈述：ind_fintype_pi {C : (forall i, Quotient (S i)) -> Prop} (f : forall a : fo
rall i, α i, C (⟦a ·⟧)) (q : forall i, Quotient (S i)) : C q
参数：forall i, Quotient (S i)；f : forall a : forall i, α i, C (⟦a ·⟧)；q : forall i
, Quotient (S i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
· 使用引理 `Quotient.list_ind`：list_ind {l : List ι} {C : (forall i in l, Quotient (
S i)) -> Prop} (f : forall a : forall i in l, α i, C (⟦a · ·⟧)) (q : forall i in
 l, Quo…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
Choice-free induction principle for quotients indexed by a finite type.
  See `Quotient.induction_on_pi` for the general version assuming `Classical.cho
ice`.
-/
lemma ind_fintype_pi {C : (∀ i, Quotient (S i)) → Prop}
    (f : ∀ a : ∀ i, α i, C (⟦a ·⟧)) (q : ∀ i, Quotient (S i)) : C q := by
  have {m : Multiset ι} (C : (∀ i ∈ m, Quotient (S i)) → Prop) :
      ∀ (_ : ∀ a : ∀ i ∈ m, α i, C (⟦a · ·⟧)) (q : ∀ i ∈ m, Quotient (S i)), C q := by
    induction m using Quotient.ind
    exact list_ind
  exact this (fun q ↦ C (q · (Finset.mem_univ _))) (fun _ ↦ f _) (fun i _ ↦ q i)

/-- Choice-free induction principle for quotients indexed by a finite type.
  See `Quotient.induction_on_pi` for the general version assuming `Classical.choice`. -/
@[elab_as_elim]
/-
**Quotient.induction_on_fintype_pi** 是 Mathlib 中的一个引理，位于命名空间 `Quotient`。
形式化陈述：induction_on_fintype_pi {C : (forall i, Quotient (S i)) -> Prop} (q : fora
ll i, Quotient (S i)) (f : forall a : forall i, α i, C (⟦a ·⟧)) : C q
参数：forall i, Quotient (S i)；q : forall i, Quotient (S i)；f : forall a : forall i
, α i, C (⟦a ·⟧)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Quotient.ind_fintype_pi`：ind_fintype_pi {C : (forall i, Quotient (S i)) 
-> Prop} (f : forall a : forall i, α i, C (⟦a ·⟧)) (q : forall i, Quotient (S i)
) : C q

--- 原说明 ---
Choice-free induction principle for quotients indexed by a finite type.
  See `Quotient.induction_on_pi` for the general version assuming `Classical.cho
ice`.
-/
lemma induction_on_fintype_pi {C : (∀ i, Quotient (S i)) → Prop}
    (q : ∀ i, Quotient (S i)) (f : ∀ a : ∀ i, α i, C (⟦a ·⟧)) : C q :=
  ind_fintype_pi f q

/-- Given a collection of setoids indexed by a fintype `ι` and a function that for each `i : ι`
  gives a term of the corresponding quotient type, then there is corresponding term in the quotient
  of the product of the setoids.
  See `Quotient.choice` for the noncomputable general version. -/
/-
**Quotient.finChoice** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：finChoice (q : forall i, Quotient (S i)) : @Quotient (forall i, α i) piSet
oid
参数：q : forall i, Quotient (S i)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
Given a collection of setoids indexed by a fintype `ι` and a function that for e
ach `i : ι`
  gives a term of the corresponding quotient type, then there is corresponding t
erm in the quotient
  of the product of the setoids.
  See `Quotient.choice` for the noncomputable general version.
-/
def finChoice (q : ∀ i, Quotient (S i)) :
    @Quotient (∀ i, α i) piSetoid := by
  let e := Equiv.subtypeQuotientEquivQuotientSubtype (fun l : List ι ↦ ∀ i, i ∈ l)
    (fun s : Multiset ι ↦ ∀ i, i ∈ s) (fun i ↦ Iff.rfl) (fun _ _ ↦ Iff.rfl) ⟨_, Finset.mem_univ⟩
  refine e.liftOn
    (fun l ↦ (listChoice fun i _ ↦ q i).map (fun a i ↦ a i (l.2 i)) ?_) ?_
  · exact fun _ _ h i ↦ h i _
  intro _ _ _
  refine ind_fintype_pi (fun a ↦ ?_) q
  simp_rw [listChoice_mk, Quotient.map_mk]
/-
**Quotient.finChoice_eq** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：finChoice_eq (a : forall i, α i) : finChoice (S
参数：a : forall i, α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Quotient.exists_rep`：∀ {α : Sort u} {s : Setoid α} (q : Quotient s), ∃ a
, ⟦a⟧ = q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.liftOn.congr_simp`：∀ {α : Sort u} {β : Sort v} {s : Setoid α} (
q q_1 : Quotient s),   q = q_1 → ∀ (f f_1 : α → β) (e_f : f = f_1) (c : ∀ (a b :
 α), a ≈ b → f a…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Quotient.map.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} {sa : Setoid α}
 {sb : Setoid β} (f f_1 : α → β) (e_f : f = f_1)   (h : ∀ ⦃a b : α⦄, a ≈ b → f a
 ≈ f b) (a a_…
· 使用定理 `Quotient.listChoice_mk`：listChoice_mk {l : List ι} (a : forall i in l, α
 i) : listChoice (S
-/
theorem finChoice_eq (a : ∀ i, α i) :
    finChoice (S := S) (⟦a ·⟧) = ⟦a⟧ := by
  dsimp [finChoice]
  obtain ⟨l, hl⟩ := (Finset.univ.val : Multiset ι).exists_rep
  simp_rw [← hl, Equiv.subtypeQuotientEquivQuotientSubtype, listChoice_mk]
  rfl
/-
**Quotient.eval_finChoice** 是 Mathlib 中的一个引理，位于命名空间 `Quotient`。
形式化陈述：eval_finChoice (f : forall i, Quotient (S i)) : eval (finChoice f) = f
参数：f : forall i, Quotient (S i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Quotient.induction_on_fintype_pi`：induction_on_fintype_pi {C : (forall i
, Quotient (S i)) -> Prop} (q : forall i, Quotient (S i)) (f : forall a : forall
 i, α i, C (⟦a ·⟧)) : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.finChoice_eq`：finChoice_eq (a : forall i, α i) : finChoice (S
-/
lemma eval_finChoice (f : ∀ i, Quotient (S i)) :
    eval (finChoice f) = f :=
  induction_on_fintype_pi f (fun a ↦ by rw [finChoice_eq]; rfl)

/-- Lift a function on `∀ i, α i` to a function on `∀ i, Quotient (S i)`. -/
/-
**Quotient.finLiftOn** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：finLiftOn (q : forall i, Quotient (S i)) (f : (forall i, α i) -> β) (h : f
orall (a b : forall i, α i), (forall i, a i ≈ b i) -> f a = f b) : β
参数：q : forall i, Quotient (S i)；f : (forall i, α i) -> β；h : forall (a b : foral
l i, α i), (forall i, a i ≈ b i) -> f a = f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a function on `∀ i, α i` to a function on `∀ i, Quotient (S i)`.
-/
def finLiftOn (q : ∀ i, Quotient (S i)) (f : (∀ i, α i) → β)
    (h : ∀ (a b : ∀ i, α i), (∀ i, a i ≈ b i) → f a = f b) : β :=
  (finChoice q).liftOn f h

@[simp]
/-
**Quotient.finLiftOn_empty** 是 Mathlib 中的一个引理，位于命名空间 `Quotient`。
形式化陈述：finLiftOn_empty [e : IsEmpty ι] (q : forall i, Quotient (S i)) : finLiftOn
 (β
参数：q : forall i, Quotient (S i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
-/
lemma finLiftOn_empty [e : IsEmpty ι] (q : ∀ i, Quotient (S i)) :
    finLiftOn (β := β) q = fun f _ ↦ f e.elim := by
  ext f h
  dsimp [finLiftOn]
  induction finChoice q using Quotient.ind
  exact h _ _ e.elim

@[simp]
/-
**Quotient.finLiftOn_mk** 是 Mathlib 中的一个引理，位于命名空间 `Quotient`。
形式化陈述：finLiftOn_mk (a : forall i, α i) : finLiftOn (S
参数：a : forall i, α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.finChoice_eq`：finChoice_eq (a : forall i, α i) : finChoice (S
-/
lemma finLiftOn_mk (a : ∀ i, α i) :
    finLiftOn (S := S) (β := β) (⟦a ·⟧) = fun f _ ↦ f a := by
  ext f h
  dsimp [finLiftOn]
  rw [finChoice_eq]
  rfl

/-- `Quotient.finChoice` as an equivalence. -/
@[simps]
/-
**Quotient.finChoiceEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：finChoiceEquiv : (forall i, Quotient (S i)) ≃ @Quotient (forall i, α i) pi
Setoid where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Quotient.finChoice` as an equivalence.
-/
def finChoiceEquiv :
    (∀ i, Quotient (S i)) ≃ @Quotient (∀ i, α i) piSetoid where
  toFun := finChoice
  invFun := eval
  left_inv q := by
    refine induction_on_fintype_pi q (fun a ↦ ?_)
    rw [finChoice_eq]
    rfl
  right_inv q := by
    induction q using Quotient.ind
    exact finChoice_eq _

/-- Recursion principle for quotients indexed by a finite type. -/
@[elab_as_elim]
/-
**Quotient.finHRecOn** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：finHRecOn {C : (forall i, Quotient (S i)) -> Sort*} (q : forall i, Quotien
t (S i)) (f : forall a : forall i, α i, C (⟦a ·⟧)) (h : forall (a b : forall i, 
α i), (forall i, a i ≈ b i) -> f a ≍ f b) : C q
参数：forall i, Quotient (S i)；q : forall i, Quotient (S i)；f : forall a : forall i
, α i, C (⟦a ·⟧)；h : forall (a b : forall i, α i), (forall i, a i ≈ b i) -> f a 
≍ f b。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Quotient.eval_finChoice`：eval_finChoice (f : forall i, Quotient (S i)) :
 eval (finChoice f) = f

--- 原说明 ---
Recursion principle for quotients indexed by a finite type.
-/
def finHRecOn {C : (∀ i, Quotient (S i)) → Sort*}
    (q : ∀ i, Quotient (S i))
    (f : ∀ a : ∀ i, α i, C (⟦a ·⟧))
    (h : ∀ (a b : ∀ i, α i), (∀ i, a i ≈ b i) → f a ≍ f b) :
    C q :=
  eval_finChoice q ▸ (finChoice q).hrecOn f h

/-- Recursion principle for quotients indexed by a finite type. -/
@[elab_as_elim]
/-
**Quotient.finRecOn** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：finRecOn {C : (forall i, Quotient (S i)) -> Sort*} (q : forall i, Quotient
 (S i)) (f : forall a : forall i, α i, C (⟦a ·⟧)) (h : forall (a b : forall i, α
 i) (h : forall i, a i ≈ b i), Eq.ndrec (f a) (funext fun i => Quotient.sound (h
 i)) = f b) : C q
参数：forall i, Quotient (S i)；q : forall i, Quotient (S i)；f : forall a : forall i
, α i, C (⟦a ·⟧)；h : forall (a b : forall i, α i) (h : forall i, a i ≈ b i), Eq.
ndrec (f a) (funext fun i => Quotient.sound (h i)) = f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion principle for quotients indexed by a finite type.
-/
def finRecOn {C : (∀ i, Quotient (S i)) → Sort*}
    (q : ∀ i, Quotient (S i))
    (f : ∀ a : ∀ i, α i, C (⟦a ·⟧))
    (h : ∀ (a b : ∀ i, α i) (h : ∀ i, a i ≈ b i),
      Eq.ndrec (f a) (funext fun i ↦ Quotient.sound (h i)) = f b) :
    C q :=
  finHRecOn q f (eqRec_heq_iff.mp <| heq_of_eq <| h · · ·)

@[simp]
/-
**Quotient.finHRecOn_mk** 是 Mathlib 中的一个引理，位于命名空间 `Quotient`。
形式化陈述：finHRecOn_mk {C : (forall i, Quotient (S i)) -> Sort*} (a : forall i, α i)
 : finHRecOn (C
参数：forall i, Quotient (S i)；a : forall i, α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `HEq.trans`：∀ {α β φ : Sort u} {a : α} {b : β} {c : φ}, a ≍ b → b ≍ c → a
 ≍ c
· 使用引理 `Quotient.eval_finChoice`：eval_finChoice (f : forall i, Quotient (S i)) :
 eval (finChoice f) = f
· 使用定理 `eqRec_heq`：∀ {α : Sort u} {φ : α → Sort v} {a a' : α} (h : a = a') (p : 
φ a), Eq.recOn h p ≍ p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.finChoice_eq`：finChoice_eq (a : forall i, α i) : finChoice (S
-/
lemma finHRecOn_mk {C : (∀ i, Quotient (S i)) → Sort*}
    (a : ∀ i, α i) :
    finHRecOn (C := C) (⟦a ·⟧) = fun f _ ↦ f a := by
  ext f h
  refine eq_of_heq ((eqRec_heq _ _).trans ?_)
  rw [finChoice_eq]
  rfl

@[simp]
/-
**Quotient.finRecOn_mk** 是 Mathlib 中的一个引理，位于命名空间 `Quotient`。
形式化陈述：finRecOn_mk {C : (forall i, Quotient (S i)) -> Sort*} (a : forall i, α i) 
: finRecOn (C
参数：forall i, Quotient (S i)；a : forall i, α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Quotient.finHRecOn_mk`：finHRecOn_mk {C : (forall i, Quotient (S i)) -> S
ort*} (a : forall i, α i) : finHRecOn (C
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finRecOn_mk {C : (∀ i, Quotient (S i)) → Sort*}
    (a : ∀ i, α i) :
    finRecOn (C := C) (⟦a ·⟧) = fun f _ ↦ f a := by
  unfold finRecOn
  simp

end Fintype

end Quotient

namespace Trunc
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {α : ι → Sort*} {β : Sort*}

/-- Given a function that for each `i : ι` gives a term of the corresponding
truncation type, then there is corresponding term in the truncation of the product. -/
/-
**Trunc.finChoice** 是 Mathlib 中的一个定义，位于命名空间 `Trunc`。
形式化陈述：finChoice (q : forall i, Trunc (α i)) : Trunc (forall i, α i)
参数：q : forall i, Trunc (α i)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
· 使用定理 `trivial`：True

--- 原说明 ---
Given a function that for each `i : ι` gives a term of the corresponding
truncation type, then there is corresponding term in the truncation of the produ
ct.
-/
def finChoice (q : ∀ i, Trunc (α i)) : Trunc (∀ i, α i) :=
  Quotient.map' id (fun _ _ _ => trivial) (Quotient.finChoice q)
/-
**Trunc.finChoice_eq** 是 Mathlib 中的一个定理，位于命名空间 `Trunc`。
形式化陈述：finChoice_eq (f : forall i, α i) : (Trunc.finChoice fun i => Trunc.mk (f i
)) = Trunc.mk f
参数：f : forall i, α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem finChoice_eq (f : ∀ i, α i) : (Trunc.finChoice fun i => Trunc.mk (f i)) = Trunc.mk f :=
  Subsingleton.elim _ _

/-- Lift a function on `∀ i, α i` to a function on `∀ i, Trunc (α i)`. -/
/-
**Trunc.finLiftOn** 是 Mathlib 中的一个定义，位于命名空间 `Trunc`。
形式化陈述：finLiftOn (q : forall i, Trunc (α i)) (f : (forall i, α i) -> β) (h : fora
ll (a b : forall i, α i), f a = f b) : β
参数：q : forall i, Trunc (α i)；f : (forall i, α i) -> β；h : forall (a b : forall i
, α i), f a = f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a function on `∀ i, α i` to a function on `∀ i, Trunc (α i)`.
-/
def finLiftOn (q : ∀ i, Trunc (α i)) (f : (∀ i, α i) → β) (h : ∀ (a b : ∀ i, α i), f a = f b) : β :=
  Quotient.finLiftOn q f (fun _ _ _ ↦ h _ _)

@[simp]
/-
**Trunc.finLiftOn_empty** 是 Mathlib 中的一个引理，位于命名空间 `Trunc`。
形式化陈述：finLiftOn_empty [e : IsEmpty ι] (q : forall i, Trunc (α i)) : finLiftOn (β
参数：q : forall i, Trunc (α i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `congrFun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort
 u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b…
· 使用引理 `Quotient.finLiftOn_empty`：finLiftOn_empty [e : IsEmpty ι] (q : forall i,
 Quotient (S i)) : finLiftOn (β
-/
lemma finLiftOn_empty [e : IsEmpty ι] (q : ∀ i, Trunc (α i)) :
    finLiftOn (β := β) q = fun f _ ↦ f e.elim :=
  funext₂ fun _ _ ↦ congrFun₂ (Quotient.finLiftOn_empty q) _ _

@[simp]
/-
**Trunc.finLiftOn_mk** 是 Mathlib 中的一个引理，位于命名空间 `Trunc`。
形式化陈述：finLiftOn_mk (a : forall i, α i) : finLiftOn (β
参数：a : forall i, α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `congrFun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort
 u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b…
· 使用引理 `Quotient.finLiftOn_mk`：finLiftOn_mk (a : forall i, α i) : finLiftOn (S
-/
lemma finLiftOn_mk (a : ∀ i, α i) :
    finLiftOn (β := β) (⟦a ·⟧) = fun f _ ↦ f a :=
  funext₂ fun _ _ ↦ congrFun₂ (Quotient.finLiftOn_mk a) _ _

/-- `Trunc.finChoice` as an equivalence. -/
@[simps]
/-
**Trunc.finChoiceEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Trunc`。
形式化陈述：finChoiceEquiv : (forall i, Trunc (α i)) ≃ Trunc (forall i, α i) where toF
un
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Trunc.finChoice` as an equivalence.
-/
def finChoiceEquiv : (∀ i, Trunc (α i)) ≃ Trunc (∀ i, α i) where
  toFun := finChoice
  invFun q i := q.map (· i)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- Recursion principle for `Trunc`s indexed by a finite type. -/
@[elab_as_elim]
/-
**Trunc.finRecOn** 是 Mathlib 中的一个定义，位于命名空间 `Trunc`。
形式化陈述：finRecOn {C : (forall i, Trunc (α i)) -> Sort*} (q : forall i, Trunc (α i)
) (f : forall a : forall i, α i, C (mk <| a ·)) (h : forall (a b : forall i, α i
), (Eq.ndrec (f a) (funext fun _ => Trunc.eq _ _)) = f b) : C q
参数：forall i, Trunc (α i)；q : forall i, Trunc (α i)；f : forall a : forall i, α i,
 C (mk <| a ·)；h : forall (a b : forall i, α i), (Eq.ndrec (f a) (funext fun _ =
> Trunc.eq _ _)) = f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion principle for `Trunc`s indexed by a finite type.
-/
def finRecOn {C : (∀ i, Trunc (α i)) → Sort*}
    (q : ∀ i, Trunc (α i))
    (f : ∀ a : ∀ i, α i, C (mk <| a ·))
    (h : ∀ (a b : ∀ i, α i), (Eq.ndrec (f a) (funext fun _ ↦ Trunc.eq _ _)) = f b) :
    C q :=
  Quotient.finRecOn q (f ·) (fun _ _ _ ↦ h _ _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Trunc.finRecOn_mk** 是 Mathlib 中的一个引理，位于命名空间 `Trunc`。
形式化陈述：finRecOn_mk {C : (forall i, Trunc (α i)) -> Sort*} (a : forall i, α i) : f
inRecOn (C
参数：forall i, Trunc (α i)；a : forall i, α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Trunc.eq`：∀ {α : Sort u_1} (a b : Trunc α), a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用引理 `Quotient.finRecOn_mk`：finRecOn_mk {C : (forall i, Quotient (S i)) -> Sor
t*} (a : forall i, α i) : finRecOn (C
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finRecOn_mk {C : (∀ i, Trunc (α i)) → Sort*}
    (a : ∀ i, α i) :
    finRecOn (C := C) (⟦a ·⟧) = fun f _ ↦ f a := by
  unfold finRecOn
  simp

end Trunc

