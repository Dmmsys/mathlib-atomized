/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Batteries.Data.List.Pairwise
public import Batteries.Tactic.GeneralizeProofs
public import Mathlib.Tactic.Order.CollectFacts
public meta import Mathlib.Util.AtomM
public meta import Mathlib.Util.Qq
public meta import Std.Data.HashMap.AdditionalOperations

/-!
# Translating linear orders to ℤ

In this file we implement the translation of a problem in any linearly ordered type to a problem in
`ℤ`. This allows us to use the `lia` tactic to solve it.

While the core algorithm of the `order` tactic is complete for the theory of linear orders in the
signature (`<`, `≤`),
it becomes incomplete in the signature with lattice operations `⊓` and `⊔`. With these operations,
the problem becomes NP-hard, and the idea is to reuse a smart and efficient procedure, such as
`lia`.

## TODO

Migrate to `grind` when it is ready.
-/

public meta section

namespace Mathlib.Tactic.Order.ToInt

variable {α : Type*} [LinearOrder α] {n : ℕ} (val : Fin n → α)

/-- The main theorem asserting the existence of a translation.
We use `Classical.choose` to turn this into a value for use in the `order` tactic,
see `toInt`.
-/
/-
**Mathlib.Tactic.Order.ToInt.exists_translation** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.Order.ToInt`。
形式化陈述：exists_translation : exists tr : Fin n -> Int, forall i j, val i <= val j 
↔ tr i <= tr j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `List.get_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ n, l.g
et n = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Perm.mem_iff`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, l₁.Perm l₂
 → (a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `List.mergeSort_perm`：∀ {α : Type u_1} (l : List α) (le : α → α → Bool), 
(l.mergeSort le).Perm l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `List.pairwise_mergeSort`：∀ {α : Type u_1} {le : α → α → Bool},   (∀ (a b
 c : α), le a b = true → le b c = true → le a c = true) →     (∀ (a b : α), (le 
a b || le b a…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Bool.or_eq_true`：∀ (a b : Bool), ((a || b) = true) = (a = true ∨ b = tru
e)
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.pairwise_iff_get`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α},
   List.Pairwise R l ↔ ∀ (i j : Fin l.length), i < j → R (l.get i) (l.get j)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The main theorem asserting the existence of a translation.
We use `Classical.choose` to turn this into a value for use in the `order` tacti
c,
see `toInt`.
-/
theorem exists_translation : ∃ tr : Fin n → ℤ, ∀ i j, val i ≤ val j ↔ tr i ≤ tr j := by
  let li := List.ofFn val
  let sli := li.mergeSort
  have (i : Fin n) : ∃ j : Fin sli.length, sli[j] = val i := by
    apply List.get_of_mem
    rw [List.Perm.mem_iff (List.mergeSort_perm _ _)]
    simp [li]
  use fun i ↦ (this i).choose
  intro i j
  simp only [Fin.getElem_fin, Int.ofNat_le]
  by_cases h_eq : val i = val j
  · simp [h_eq]
  generalize_proofs _ hi hj
  rw [← hi.choose_spec, ← hj.choose_spec] at h_eq
  conv_lhs => rw [← hi.choose_spec, ← hj.choose_spec]
  have := li.pairwise_mergeSort (le := fun a b ↦ decide (a ≤ b))
      (fun a b c ↦ by simpa using le_trans) (by simpa using le_total)
  rw [List.pairwise_iff_get] at this
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose! h
    exact lt_of_le_of_ne (by simpa using (this hj.choose hi.choose (by simpa)))
      (fun h ↦ h_eq (h.symm))
  · simpa using this hi.choose hj.choose (by apply lt_of_le_of_ne h; contrapose h_eq; simp [h_eq])

/-- Auxiliary definition used by the `order` tactic to transfer facts in a linear order to `ℤ`. -/
/-
**Mathlib.Tactic.Order.ToInt.toInt** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Ord
er.ToInt`。
形式化陈述：toInt (k : Fin n) : Int
参数：k : Fin n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Order.ToInt.exists_translation`：exists_translation : exis
ts tr : Fin n -> Int, forall i j, val i <= val j ↔ tr i <= tr j

--- 原说明 ---
Auxiliary definition used by the `order` tactic to transfer facts in a linear or
der to `ℤ`.
-/
noncomputable def toInt (k : Fin n) : ℤ :=
  (exists_translation val).choose k

variable (i j k : Fin n)
/-
**Mathlib.Tactic.Order.ToInt.toInt_le_toInt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.Order.ToInt`。
形式化陈述：toInt_le_toInt : toInt val i <= toInt val j ↔ val i <= val j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Order.ToInt.exists_translation`：exists_translation : exis
ts tr : Fin n -> Int, forall i j, val i <= val j ↔ tr i <= tr j
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toInt_le_toInt : toInt val i ≤ toInt val j ↔ val i ≤ val j := by
  simp [toInt, (exists_translation val).choose_spec]
/-
**Mathlib.Tactic.Order.ToInt.toInt_lt_toInt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.Order.ToInt`。
形式化陈述：toInt_lt_toInt : toInt val i < toInt val j ↔ val i < val j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Mathlib.Tactic.Order.ToInt.toInt_le_toInt`：toInt_le_toInt : toInt val i 
<= toInt val j ↔ val i <= val j
-/
theorem toInt_lt_toInt : toInt val i < toInt val j ↔ val i < val j := by
  simpa using (toInt_le_toInt val j i).not
/-
**Mathlib.Tactic.Order.ToInt.toInt_eq_toInt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.Order.ToInt`。
形式化陈述：toInt_eq_toInt : toInt val i = toInt val j ↔ val i = val j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toInt_eq_toInt : toInt val i = toInt val j ↔ val i = val j := by
  simp [toInt_le_toInt, le_antisymm_iff]
/-
**Mathlib.Tactic.Order.ToInt.toInt_ne_toInt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.Order.ToInt`。
形式化陈述：toInt_ne_toInt : toInt val i != toInt val j ↔ val i != val j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Mathlib.Tactic.Order.ToInt.toInt_eq_toInt`：toInt_eq_toInt : toInt val i 
= toInt val j ↔ val i = val j
-/
theorem toInt_ne_toInt : toInt val i ≠ toInt val j ↔ val i ≠ val j := by
  simpa using (toInt_eq_toInt val i j).not
/-
**Mathlib.Tactic.Order.ToInt.toInt_nle_toInt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Tactic.Order.ToInt`。
形式化陈述：toInt_nle_toInt : ¬toInt val i <= toInt val j ↔ ¬val i <= val j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Order.ToInt.toInt_lt_toInt`：toInt_lt_toInt : toInt val i 
< toInt val j ↔ val i < val j
-/
theorem toInt_nle_toInt : ¬toInt val i ≤ toInt val j ↔ ¬val i ≤ val j := by
  simpa using toInt_lt_toInt val j i
/-
**Mathlib.Tactic.Order.ToInt.toInt_nlt_toInt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Tactic.Order.ToInt`。
形式化陈述：toInt_nlt_toInt : ¬toInt val i < toInt val j ↔ ¬val i < val j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Order.ToInt.toInt_le_toInt`：toInt_le_toInt : toInt val i 
<= toInt val j ↔ val i <= val j
-/
theorem toInt_nlt_toInt : ¬toInt val i < toInt val j ↔ ¬val i < val j := by
  simpa using toInt_le_toInt val j i
/-
**Mathlib.Tactic.Order.ToInt.toInt_sup_toInt_eq_toInt** 是 Mathlib 中的一个定理，位于命名空间 
`Mathlib.Tactic.Order.ToInt`。
形式化陈述：toInt_sup_toInt_eq_toInt : toInt val i ⊔ toInt val j = toInt val k ↔ val i
 ⊔ val j = val k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toInt_sup_toInt_eq_toInt :
    toInt val i ⊔ toInt val j = toInt val k ↔ val i ⊔ val j = val k := by
  simp [le_antisymm_iff, sup_le_iff, le_sup_iff, toInt_le_toInt]
/-
**Mathlib.Tactic.Order.ToInt.toInt_inf_toInt_eq_toInt** 是 Mathlib 中的一个定理，位于命名空间 
`Mathlib.Tactic.Order.ToInt`。
形式化陈述：toInt_inf_toInt_eq_toInt : toInt val i ⊓ toInt val j = toInt val k ↔ val i
 ⊓ val j = val k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toInt_inf_toInt_eq_toInt :
    toInt val i ⊓ toInt val j = toInt val k ↔ val i ⊓ val j = val k := by
  simp [le_antisymm_iff, inf_le_iff, le_inf_iff, toInt_le_toInt]

open Lean Meta Qq

/-- Given an array `atoms : Array α`, create an expression representing a function
`f : Fin atoms.size → α` such that `f n` is defeq to `atoms[n]` for `n : Fin atoms.size`. -/
/-
**Mathlib.Tactic.Order.ToInt.mkFinFun** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.
Order.ToInt`。
形式化陈述：mkFinFun {u : Level} {α : Q(Type $u)} (atoms : Array Q($α)) : MetaM Expr
参数：Type $u；atoms : Array Q($α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an array `atoms : Array α`, create an expression representing a function
`f : Fin atoms.size → α` such that `f n` is defeq to `atoms[n]` for `n : Fin ato
ms.size`.
-/
def mkFinFun {u : Level} {α : Q(Type $u)} (atoms : Array Q($α)) : MetaM Expr := do
  if h : atoms.isEmpty then
    return q(Fin.elim0 : Fin 0 → $α)
  else
    let rarray := RArray.ofArray atoms (by simpa [Array.size_pos_iff] using h)
    let rarrayExpr : Q(RArray $α) ← rarray.toExpr α (fun x ↦ x)
    haveI m : Q(ℕ) := mkNatLit atoms.size
    return q(fun (x : Fin $m) ↦ ($rarrayExpr).get x.val)

/-- Translates a set of values in a linear ordered type to `ℤ`,
preserving all the facts except for `.isTop` and `.isBot`. We assume that these facts are filtered
at the preprocessing step. -/
/-
**Mathlib.Tactic.Order.ToInt.translateToInt** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.T
actic.Order.ToInt`。
形式化陈述：translateToInt {u : Lean.Level} (type : Q(Type u)) (inst : Q(LinearOrder $
type)) (facts : Array AtomicFact) : AtomM Std.HashMap Nat Q(Int) × Array AtomicF
act
参数：type : Q(Type u)；inst : Q(LinearOrder $type)；facts : Array AtomicFact。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Translates a set of values in a linear ordered type to `ℤ`,
preserving all the facts except for `.isTop` and `.isBot`. We assume that these 
facts are filtered
at the preprocessing step.
-/
def translateToInt {u : Lean.Level} (type : Q(Type u)) (inst : Q(LinearOrder $type))
    (facts : Array AtomicFact) :
    AtomM <| Std.HashMap ℕ Q(ℤ) × Array AtomicFact := do
  let mut idxToAtom : Std.HashMap Nat Q($type) := ∅
  for atom in (← get).atoms do
    -- `atoms` contains atoms for all types we are working on, so here we need to filter only
    -- those of type `type`
    if ← withReducible <| isDefEq type (← inferType atom) then
      idxToAtom := idxToAtom.insert idxToAtom.size atom
  haveI nE : Q(ℕ) := mkNatLitQ idxToAtom.size
  haveI finFun : Q(Fin $nE → $type) :=
    ← mkFinFun (Array.ofFn fun (n : Fin idxToAtom.size) => idxToAtom[n]!)
  let toFinUnsafe : ℕ → Q(Fin $nE) := fun k =>
    haveI kE := mkNatLitQ k
    haveI heq : decide ($kE < $nE) =Q true := ⟨⟩
    q(⟨$kE, of_decide_eq_true $heq⟩)
  return Prod.snd <| facts.foldl (fun (curr, map, facts) fact =>
    match fact with
    | .eq lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q($finFun $lhsFin = $finFun $rhsFin) := prf
        .eq lhs rhs q((toInt_eq_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .ne lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q($finFun $lhsFin ≠ $finFun $rhsFin) := prf
        .ne lhs rhs q((toInt_ne_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .le lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q($finFun $lhsFin ≤ $finFun $rhsFin) := prf
        .le lhs rhs q((toInt_le_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .lt lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q($finFun $lhsFin < $finFun $rhsFin) := prf
        .lt lhs rhs q((toInt_lt_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .nle lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q(¬$finFun $lhsFin ≤ $finFun $rhsFin) := prf
        .nle lhs rhs q((toInt_nle_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .nlt lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q(¬$finFun $lhsFin < $finFun $rhsFin) := prf
        .nlt lhs rhs q((toInt_nlt_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .isBot _
    | .isTop _ => (curr, map, facts)
    | .isSup lhs rhs val =>
      haveI lhsFin := toFinUnsafe lhs
      haveI rhsFin := toFinUnsafe rhs
      haveI valFin := toFinUnsafe val
      haveI heq : max («$finFun» «$lhsFin») («$finFun» «$rhsFin») =Q «$finFun» «$valFin» := ⟨⟩
      (curr + 1, map.insert curr q(toInt $finFun $lhsFin ⊔ toInt $finFun $rhsFin),
        (facts.push (.isSup lhs rhs curr)).push (.eq curr val
          q((toInt_sup_toInt_eq_toInt $finFun $lhsFin $rhsFin $valFin).mpr $heq)
        )
      )
    | .isInf lhs rhs val =>
      haveI lhsFin := toFinUnsafe lhs
      haveI rhsFin := toFinUnsafe rhs
      haveI valFin := toFinUnsafe val
      haveI heq : min («$finFun» «$lhsFin») («$finFun» «$rhsFin») =Q «$finFun» «$valFin» := ⟨⟩
      (curr + 1, map.insert curr q(toInt $finFun $lhsFin ⊓ toInt $finFun $rhsFin),
        (facts.push (.isInf lhs rhs curr)).push (.eq curr val
          q((toInt_inf_toInt_eq_toInt $finFun $lhsFin $rhsFin $valFin).mpr $heq)
        )
      ))
    (idxToAtom.size, idxToAtom.map fun k _ =>
      haveI kFin := toFinUnsafe k
      q(toInt $finFun $kFin), Array.emptyWithCapacity idxToAtom.size)

end Mathlib.Tactic.Order.ToInt

export Mathlib.Tactic.Order.ToInt (translateToInt)

