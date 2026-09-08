/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!

# General-Valued Constraint Satisfaction Problems

General-Valued CSP is a very broad class of problems in discrete optimization.
General-Valued CSP subsumes Min-Cost-Hom (including 3-SAT for example) and Finite-Valued CSP.

## Main definitions
* `ValuedCSP`: A VCSP template; fixes a domain, a codomain, and allowed cost functions.
* `ValuedCSP.Term`: One summand in a VCSP instance; calls a concrete function from given template.
* `ValuedCSP.Term.evalSolution`: An evaluation of the VCSP term for given solution.
* `ValuedCSP.Instance`: An instance of a VCSP problem over given template.
* `ValuedCSP.Instance.evalSolution`: An evaluation of the VCSP instance for given solution.
* `ValuedCSP.Instance.IsOptimumSolution`: Is given solution a minimum of the VCSP instance?
* `Function.HasMaxCutProperty`: Can given binary function express the Max-Cut problem?
* `FractionalOperation`: Multiset of operations on given domain of the same arity.
* `FractionalOperation.IsSymmetricFractionalPolymorphismFor`: Is given fractional operation a
  symmetric fractional polymorphism for given VCSP template?

## References
* [D. A. Cohen, M. C. Cooper, P. Creed, P. G. Jeavons, S. Živný,
  *An Algebraic Theory of Complexity for Discrete Optimisation*][cohen2012]

-/

@[expose] public section

/-- A template for a valued CSP problem over a domain `D` with costs in `C`.
Regarding `C` we want to support `Bool`, `Nat`, `ENat`, `Int`, `Rat`, `NNRat`,
`Real`, `NNReal`, `EReal`, `ENNReal`, and tuples made of any of those types. -/
@[nolint unusedArguments]
/-
**ValuedCSP** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ValuedCSP (D C : Type*) [AddCommMonoid C] [PartialOrder C] [IsOrderedAddMo
noid C]
参数：D C : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A template for a valued CSP problem over a domain `D` with costs in `C`.
Regarding `C` we want to support `Bool`, `Nat`, `ENat`, `Int`, `Rat`, `NNRat`,
`Real`, `NNReal`, `EReal`, `ENNReal`, and tuples made of any of those types.
-/
abbrev ValuedCSP (D C : Type*) [AddCommMonoid C] [PartialOrder C] [IsOrderedAddMonoid C] :=
  Set (Σ (n : ℕ), (Fin n → D) → C) -- Cost functions `D^n → C` for any `n`

variable {D C : Type*} [AddCommMonoid C] [PartialOrder C] [IsOrderedAddMonoid C]

/-- A term in a valued CSP instance over the template `Γ`. -/
/-
**ValuedCSP.Term** 是 Mathlib 中的一个归纳类型，位于命名空间 `ValuedCSP`。
形式化陈述：{D : Type u_1} →   {C : Type u_2} →     [inst : AddCommMonoid C] →       [
inst_1 : PartialOrder C] →         [inst_2 : IsOrderedAddMonoid C] → ValuedCSP D
 C → Type u_3 → Type (max (max u_1 u_2) u_3)
参数：max (max u_1 u_2) u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A term in a valued CSP instance over the template `Γ`.
-/
structure ValuedCSP.Term (Γ : ValuedCSP D C) (ι : Type*) where
  /-- Arity of the function -/
  n : ℕ
  /-- Which cost function is instantiated -/
  f : (Fin n → D) → C
  /-- The cost function comes from the template -/
  inΓ : ⟨n, f⟩ ∈ Γ
  /-- Which variables are plugged as arguments to the cost function -/
  app : Fin n → ι

/-- Evaluation of a `Γ` term `t` for given solution `x`. -/
/-
**ValuedCSP.Term.evalSolution** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ValuedCSP.Term.evalSolution {Γ : ValuedCSP D C} {ι : Type*} (t : Γ.Term ι)
 (x : ι -> D) : C
参数：t : Γ.Term ι；x : ι -> D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation of a `Γ` term `t` for given solution `x`.
-/
def ValuedCSP.Term.evalSolution {Γ : ValuedCSP D C} {ι : Type*}
    (t : Γ.Term ι) (x : ι → D) : C :=
  t.f (x ∘ t.app)

/-- A valued CSP instance over the template `Γ` with variables indexed by `ι`. -/
/-
**ValuedCSP.Instance** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ValuedCSP.Instance (Γ : ValuedCSP D C) (ι : Type*) : Type _
参数：Γ : ValuedCSP D C；ι : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A valued CSP instance over the template `Γ` with variables indexed by `ι`.
-/
abbrev ValuedCSP.Instance (Γ : ValuedCSP D C) (ι : Type*) : Type _ :=
  Multiset (Γ.Term ι)

/-- Evaluation of a `Γ` instance `I` for given solution `x`. -/
/-
**ValuedCSP.Instance.evalSolution** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ValuedCSP.Instance.evalSolution {Γ : ValuedCSP D C} {ι : Type*} (I : Γ.Ins
tance ι) (x : ι -> D) : C
参数：I : Γ.Instance ι；x : ι -> D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation of a `Γ` instance `I` for given solution `x`.
-/
def ValuedCSP.Instance.evalSolution {Γ : ValuedCSP D C} {ι : Type*}
    (I : Γ.Instance ι) (x : ι → D) : C :=
  (I.map (·.evalSolution x)).sum

/-- Condition for `x` being an optimum solution (min) to given `Γ` instance `I`. -/
/-
**ValuedCSP.Instance.IsOptimumSolution** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ValuedCSP.Instance.IsOptimumSolution {Γ : ValuedCSP D C} {ι : Type*} (I : 
Γ.Instance ι) (x : ι -> D) : Prop
参数：I : Γ.Instance ι；x : ι -> D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Condition for `x` being an optimum solution (min) to given `Γ` instance `I`.
-/
def ValuedCSP.Instance.IsOptimumSolution {Γ : ValuedCSP D C} {ι : Type*}
    (I : Γ.Instance ι) (x : ι → D) : Prop :=
  ∀ y : ι → D, I.evalSolution x ≤ I.evalSolution y

/-- Function `f` has Max-Cut property at labels `a` and `b` when `argmin f` is exactly
`{ ![a, b], ![b, a] }`. -/
/-
**Function.HasMaxCutPropertyAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.HasMaxCutPropertyAt (f : (Fin 2 -> D) -> C) (a b : D) : Prop
参数：f : (Fin 2 -> D) -> C；a b : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Function `f` has Max-Cut property at labels `a` and `b` when `argmin f` is exact
ly
`{ ![a, b], ![b, a] }`.
-/
def Function.HasMaxCutPropertyAt (f : (Fin 2 → D) → C) (a b : D) : Prop :=
  f ![a, b] = f ![b, a] ∧
    ∀ x y : D, f ![a, b] ≤ f ![x, y] ∧ (f ![a, b] = f ![x, y] → a = x ∧ b = y ∨ a = y ∧ b = x)

/-- Function `f` has Max-Cut property at some two non-identical labels. -/
/-
**Function.HasMaxCutProperty** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.HasMaxCutProperty (f : (Fin 2 -> D) -> C) : Prop
参数：f : (Fin 2 -> D) -> C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Function `f` has Max-Cut property at some two non-identical labels.
-/
def Function.HasMaxCutProperty (f : (Fin 2 → D) → C) : Prop :=
  ∃ a b : D, a ≠ b ∧ f.HasMaxCutPropertyAt a b

/-- Fractional operation is a finite unordered collection of D^m → D possibly with duplicates. -/
/-
**FractionalOperation** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：FractionalOperation (D : Type*) (m : Nat) : Type _
参数：D : Type*；m : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fractional operation is a finite unordered collection of D^m → D possibly with d
uplicates.
-/
abbrev FractionalOperation (D : Type*) (m : ℕ) : Type _ :=
  Multiset ((Fin m → D) → D)

variable {m : ℕ}

/-- Arity of the "output" of the fractional operation. -/
@[simp]
/-
**FractionalOperation.size** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FractionalOperation.size (ω : FractionalOperation D m) : Nat
参数：ω : FractionalOperation D m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Arity of the "output" of the fractional operation.
-/
def FractionalOperation.size (ω : FractionalOperation D m) : ℕ := ω.card

/-- Fractional operation is valid iff nonempty. -/
/-
**FractionalOperation.IsValid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FractionalOperation.IsValid (ω : FractionalOperation D m) : Prop
参数：ω : FractionalOperation D m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fractional operation is valid iff nonempty.
-/
def FractionalOperation.IsValid (ω : FractionalOperation D m) : Prop :=
  ω ≠ ∅

/-- Valid fractional operation contains an operation. -/
/-
**FractionalOperation.IsValid.contains** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FractionalOperation.IsValid.contains {ω : FractionalOperation D m} (valid 
: ω.IsValid) : exists g : (Fin m -> D) -> D, g in ω
参数：valid : ω.IsValid。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.exists_mem_of_ne_zero`：exists_mem_of_ne_zero {s : Multiset α} :
 s != 0 -> exists a : α, a in s

--- 原说明 ---
Valid fractional operation contains an operation.
-/
lemma FractionalOperation.IsValid.contains {ω : FractionalOperation D m} (valid : ω.IsValid) :
    ∃ g : (Fin m → D) → D, g ∈ ω :=
  Multiset.exists_mem_of_ne_zero valid

/-- Fractional operation applied to a transposed table of values. -/
/-
**FractionalOperation.tt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FractionalOperation.tt {ι : Type*} (ω : FractionalOperation D m) (x : Fin 
m -> ι -> D) : Multiset (ι -> D)
参数：ω : FractionalOperation D m；x : Fin m -> ι -> D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fractional operation applied to a transposed table of values.
-/
def FractionalOperation.tt {ι : Type*} (ω : FractionalOperation D m) (x : Fin m → ι → D) :
    Multiset (ι → D) :=
  ω.map (fun (g : (Fin m → D) → D) (i : ι) => g ((Function.swap x) i))

/-- Cost function admits given fractional operation, i.e., `ω` improves `f` in the `≤` sense. -/
/-
**Function.AdmitsFractional** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.AdmitsFractional {n : Nat} (f : (Fin n -> D) -> C) (ω : Fractiona
lOperation D m) : Prop
参数：f : (Fin n -> D) -> C；ω : FractionalOperation D m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cost function admits given fractional operation, i.e., `ω` improves `f` in the `
≤` sense.
-/
def Function.AdmitsFractional {n : ℕ} (f : (Fin n → D) → C) (ω : FractionalOperation D m) : Prop :=
  ∀ x : (Fin m → (Fin n → D)),
    m • ((ω.tt x).map f).sum ≤ ω.size • Finset.univ.sum (fun i => f (x i))

/-- Fractional operation is a fractional polymorphism for given VCSP template. -/
/-
**FractionalOperation.IsFractionalPolymorphismFor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FractionalOperation.IsFractionalPolymorphismFor (ω : FractionalOperation D
 m) (Γ : ValuedCSP D C) : Prop
参数：ω : FractionalOperation D m；Γ : ValuedCSP D C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fractional operation is a fractional polymorphism for given VCSP template.
-/
def FractionalOperation.IsFractionalPolymorphismFor
    (ω : FractionalOperation D m) (Γ : ValuedCSP D C) : Prop :=
  ∀ f ∈ Γ, f.snd.AdmitsFractional ω

/-- Fractional operation is symmetric. -/
/-
**FractionalOperation.IsSymmetric** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FractionalOperation.IsSymmetric (ω : FractionalOperation D m) : Prop
参数：ω : FractionalOperation D m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fractional operation is symmetric.
-/
def FractionalOperation.IsSymmetric (ω : FractionalOperation D m) : Prop :=
  ∀ x y : (Fin m → D), List.Perm (List.ofFn x) (List.ofFn y) → ∀ g ∈ ω, g x = g y

/-- Fractional operation is a symmetric fractional polymorphism for given VCSP template. -/
/-
**FractionalOperation.IsSymmetricFractionalPolymorphismFor** 是 Mathlib 中的一个定义，位于
命名空间 ``。
形式化陈述：FractionalOperation.IsSymmetricFractionalPolymorphismFor (ω : FractionalOp
eration D m) (Γ : ValuedCSP D C) : Prop
参数：ω : FractionalOperation D m；Γ : ValuedCSP D C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fractional operation is a symmetric fractional polymorphism for given VCSP templ
ate.
-/
def FractionalOperation.IsSymmetricFractionalPolymorphismFor
    (ω : FractionalOperation D m) (Γ : ValuedCSP D C) : Prop :=
  ω.IsFractionalPolymorphismFor Γ ∧ ω.IsSymmetric
/-
**Function.HasMaxCutPropertyAt.rows_lt_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.HasMaxCutPropertyAt.rows_lt_aux {C : Type*} [PartialOrder C] {f :
 (Fin 2 -> D) -> C} {a b : D} (mcf : f.HasMaxCutPropertyAt a b) (hab : a != b) {
ω : FractionalOperation D 2} (symmega : ω.IsSymmetric) {r : Fin 2 -> D} (rin : r
 in (ω.tt ![![a, b], ![b, a]])) : f ![a, b] < f r
参数：Fin 2 -> D；mcf : f.HasMaxCutPropertyAt a b；hab : a != b；symmega : ω.IsSymmetr
ic；rin : r in (ω.tt ![![a, b], ![b, a]])。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.ofFn_succ`：∀ {α : Type u_1} {n : ℕ} {f : Fin (n + 1) → α}, List.ofF
n f = f 0 :: List.ofFn fun i => f i.succ
· 使用定理 `List.ofFn_zero`：∀ {α : Type u_1} {f : Fin 0 → α}, List.ofFn f = []
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `FractionalOperation.tt.eq_1`：∀ {D : Type u_1} {m : ℕ} {ι : Type u_3} (ω 
: FractionalOperation D m) (x : Fin m → ι → D),   ω.tt x = Multiset.map (fun g i
 => g (Function.s…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用引理 `Matrix.const_fin1_eq`：const_fin1_eq (x : α) : (fun _ : Fin 1 => x) = ![x
]
-/
lemma Function.HasMaxCutPropertyAt.rows_lt_aux {C : Type*} [PartialOrder C]
    {f : (Fin 2 → D) → C} {a b : D} (mcf : f.HasMaxCutPropertyAt a b) (hab : a ≠ b)
    {ω : FractionalOperation D 2} (symmega : ω.IsSymmetric)
    {r : Fin 2 → D} (rin : r ∈ (ω.tt ![![a, b], ![b, a]])) :
    f ![a, b] < f r := by
  rw [FractionalOperation.tt, Multiset.mem_map] at rin
  rw [show r = ![r 0, r 1] by simp [← List.ofFn_inj]]
  apply lt_of_le_of_ne (mcf.right (r 0) (r 1)).left
  intro equ
  have asymm : r 0 ≠ r 1 := by
    rcases (mcf.right (r 0) (r 1)).right equ with ⟨ha0, hb1⟩ | ⟨ha1, hb0⟩
    · rw [ha0, hb1] at hab
      exact hab
    · rw [ha1, hb0] at hab
      exact hab.symm
  apply asymm
  obtain ⟨o, in_omega, rfl⟩ := rin
  change o (fun j => ![![a, b], ![b, a]] j 0) = o (fun j => ![![a, b], ![b, a]] j 1)
  convert! symmega ![a, b] ![b, a] (by simp [List.Perm.swap]) o in_omega using 2 <;>
    simp [Matrix.const_fin1_eq]

variable {C : Type*} [AddCommMonoid C] [PartialOrder C] [IsOrderedCancelAddMonoid C]
/-
**Function.HasMaxCutProperty.forbids_commutativeFractionalPolymorphism** 是 Mathl
ib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.HasMaxCutProperty.forbids_commutativeFractionalPolymorphism {f : 
(Fin 2 -> D) -> C} (mcf : f.HasMaxCutProperty) {ω : FractionalOperation D 2} (va
lid : ω.IsValid) (symmega : ω.IsSymmetric) : ¬ f.AdmitsFractional ω
参数：Fin 2 -> D；mcf : f.HasMaxCutProperty；valid : ω.IsValid；symmega : ω.IsSymmetri
c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.sum_lt_sum`：∀ {ι : Type u_1} {α : Type u_2} [inst : AddCommMono
id α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α]   [AddLeftStrictMono α]
 {s : Mul…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Function.HasMaxCutPropertyAt.rows_lt_aux`：Function.HasMaxCutPropertyAt.r
ows_lt_aux {C : Type*} [PartialOrder C] {f : (Fin 2 -> D) -> C} {a b : D} (mcf :
 f.HasMaxCutPropertyAt a b) (h…
· 使用引理 `FractionalOperation.IsValid.contains`：FractionalOperation.IsValid.contai
ns {ω : FractionalOperation D m} (valid : ω.IsValid) : exists g : (Fin m -> D) -
> D, g in ω
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
（共 36 条，此处仅展示前 30 条）
-/
lemma Function.HasMaxCutProperty.forbids_commutativeFractionalPolymorphism
    {f : (Fin 2 → D) → C} (mcf : f.HasMaxCutProperty)
    {ω : FractionalOperation D 2} (valid : ω.IsValid) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω := by
  intro contr
  obtain ⟨a, b, hab, mcfab⟩ := mcf
  specialize contr ![![a, b], ![b, a]]
  rw [Fin.sum_univ_two', ← mcfab.left, ← two_nsmul] at contr
  have sharp :
    2 • ((ω.tt ![![a, b], ![b, a]]).map (fun _ => f ![a, b])).sum <
    2 • ((ω.tt ![![a, b], ![b, a]]).map f).sum := by
    have half_sharp :
      ((ω.tt ![![a, b], ![b, a]]).map (fun _ => f ![a, b])).sum <
      ((ω.tt ![![a, b], ![b, a]]).map f).sum := by
      apply Multiset.sum_lt_sum
      · intro r rin
        exact le_of_lt (mcfab.rows_lt_aux hab symmega rin)
      · obtain ⟨g, _⟩ := valid.contains
        have : (fun i => g ((Function.swap ![![a, b], ![b, a]]) i)) ∈ ω.tt ![![a, b], ![b, a]] := by
          simp only [FractionalOperation.tt, Multiset.mem_map]
          use g
        exact ⟨_, this, mcfab.rows_lt_aux hab symmega this⟩
    rw [two_nsmul, two_nsmul]
    exact add_lt_add half_sharp half_sharp
  have impos : 2 • (ω.map (fun _ => f ![a, b])).sum < ω.size • 2 • f ![a, b] := by
    convert! lt_of_lt_of_le sharp contr
    simp [FractionalOperation.tt, Multiset.map_map]
  have rhs_swap : ω.size • 2 • f ![a, b] = 2 • ω.size • f ![a, b] := nsmul_left_comm ..
  have distrib : (ω.map (fun _ => f ![a, b])).sum = ω.size • f ![a, b] := by simp
  rw [rhs_swap, distrib] at impos
  exact ne_of_lt impos rfl
