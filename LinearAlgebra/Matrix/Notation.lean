/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Fin.Tuple
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Fin
public meta import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Matrix and vector notation

This file includes `simp` lemmas for applying operations in `Data.Matrix.Basic` to values built out
of the matrix notation `![a, b] = vecCons a (vecCons b vecEmpty)` defined in
`Data.Fin.VecNotation`.

This also provides the new notation `!![a, b; c, d] = Matrix.of ![![a, b], ![c, d]]`.
This notation also works for empty matrices; `!![,,,] : Matrix (Fin 0) (Fin 3)` and
`!![;;;] : Matrix (Fin 3) (Fin 0)`.

## Implementation notes

The `simp` lemmas require that one of the arguments is of the form `vecCons _ _`.
This ensures `simp` works with entries only when (some) entries are already given.
In other words, this notation will only appear in the output of `simp` if it
already appears in the input.

## Notation

This file provide notation `!![a, b; c, d]` for matrices, which corresponds to
`Matrix.of ![![a, b], ![c, d]]`.

## Examples

Examples of usage can be found in the `MathlibTest/matrix.lean` file.
-/

@[expose] public section

namespace Matrix

universe u uₘ uₙ uₒ

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

open Matrix

section toExpr

open Lean Qq

open Qq in
/-- `Matrix.mkLiteralQ !![a, b; c, d]` produces the term `q(!![$a, $b; $c, $d])`. -/
meta def mkLiteralQ {u : Level} {α : Q(Type u)} {m n : Nat} (elems : Matrix (Fin m) (Fin n) Q($α)) :
    Q(Matrix (Fin $m) (Fin $n) $α) :=
  let elems := PiFin.mkLiteralQ (α := q(Fin $n → $α)) fun i => PiFin.mkLiteralQ fun j => elems i j
  q(Matrix.of $elems)

/-- Matrices can be reflected whenever their entries can. We insert a `Matrix.of` to
prevent immediate decay to a function. -/
protected meta instance toExpr [ToLevel.{u}] [ToLevel.{uₘ}] [ToLevel.{uₙ}]
    [Lean.ToExpr α] [Lean.ToExpr m'] [Lean.ToExpr n'] [Lean.ToExpr (m' → n' → α)] :
    Lean.ToExpr (Matrix m' n' α) :=
  have eα : Q(Type $(toLevel.{u})) := toTypeExpr α
  have em' : Q(Type $(toLevel.{uₘ})) := toTypeExpr m'
  have en' : Q(Type $(toLevel.{uₙ})) := toTypeExpr n'
  { toTypeExpr :=
    q(Matrix $eα $em' $en')
    toExpr := fun M =>
      have eM : Q($em' → $en' → $eα) := toExpr (show m' → n' → α from M)
      q(Matrix.of $eM) }

end toExpr

section Parser
open Lean Meta Elab Term Macro TSyntax PrettyPrinter.Delaborator SubExpr

/-- Notation for m×n matrices, aka `Matrix (Fin m) (Fin n) α`.

For instance:
* `!![a, b, c; d, e, f]` is the matrix with two rows and three columns, of type
  `Matrix (Fin 2) (Fin 3) α`
* `!![a, b, c]` is a row vector of type `Matrix (Fin 1) (Fin 3) α` (see also `Matrix.row`).
* `!![a; b; c]` is a column vector of type `Matrix (Fin 3) (Fin 1) α` (see also `Matrix.col`).

This notation implements some special cases:

* `![,,]`, with `n` `,`s, is a term of type `Matrix (Fin 0) (Fin n) α`
* `![;;]`, with `m` `;`s, is a term of type `Matrix (Fin m) (Fin 0) α`
* `![]` is the 0×0 matrix

Note that vector notation is provided elsewhere (by `Matrix.vecNotation`) as `![a, b, c]`.
Under the hood, `!![a, b, c; d, e, f]` is syntax for `Matrix.of ![![a, b, c], ![d, e, f]]`.
-/
syntax (name := matrixNotation)
  "!![" ppRealGroup(sepBy1(ppGroup(term,+,?), ";", "; ", allowTrailingSep)) "]" : term

@[inherit_doc matrixNotation]
syntax (name := matrixNotationRx0) "!![" ";"+ "]" : term
@[inherit_doc matrixNotation]
syntax (name := matrixNotation0xC) "!![" ","* "]" : term

macro_rules
  | `(!![$[$[$rows],*];*]) => do
    let m := rows.size
    let n := if h : 0 < m then rows[0].size else 0
    let rowVecs ← rows.mapM fun row : Array Term => do
      unless row.size = n do
        Macro.throwErrorAt (mkNullNode row) s!"\
          Rows must be of equal length; this row has {row.size} items, \
          the previous rows have {n}"
      `(![$row,*])
    `(@Matrix.of (Fin $(quote m)) (Fin $(quote n)) _ ![$rowVecs,*])
  | `(!![$[;%$semicolons]*]) => do
    let emptyVec ← `(![])
    let emptyVecs := semicolons.map (fun _ => emptyVec)
    `(@Matrix.of (Fin $(quote semicolons.size)) (Fin 0) _ ![$emptyVecs,*])
  | `(!![$[,%$commas]*]) => `(@Matrix.of (Fin 0) (Fin $(quote commas.size)) _ ![])

/-- Delaborator for the `!![]` notation. -/
@[app_delab DFunLike.coe]
meta def delabMatrixNotation : Delab := whenNotPPOption getPPExplicit <|
  whenPPOption getPPNotation <|
  withOverApp 6 do
    let mkApp3 (.const ``Matrix.of _) (.app (.const ``Fin _) em) (.app (.const ``Fin _) en) _ :=
      (← getExpr).appFn!.appArg! | failure
    let some m ← withNatValue em (pure ∘ some) | failure
    let some n ← withNatValue en (pure ∘ some) | failure
    withAppArg do
      if m = 0 then
        guard <| (← getExpr).isAppOfArity ``vecEmpty 1
        let commas := .replicate n (mkAtom ",")
        `(!![$[,%$commas]*])
      else
        if n = 0 then
          let `(![$[![]%$evecs],*]) ← delab | failure
          `(!![$[;%$evecs]*])
        else
          let `(![$[![$[$melems],*]],*]) ← delab | failure
          `(!![$[$[$melems],*];*])

end Parser

variable (a b : ℕ)

/-- Use `![...]` notation for displaying a `Fin`-indexed matrix, for example:

```
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]
```
-/
/-
**Matrix.repr** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：repr [Repr α] : Repr (Matrix (Fin m) (Fin n) α) where reprPrec f _p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use `![...]` notation for displaying a `Fin`-indexed matrix, for example:

```
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]
```
-/
instance repr [Repr α] : Repr (Matrix (Fin m) (Fin n) α) where
  reprPrec f _p :=
    (Std.Format.bracket "!![" · "]") <|
      (Std.Format.joinSep · (";" ++ Std.Format.line)) <|
        (List.finRange m).map fun i =>
          Std.Format.fill <|  -- wrap line in a single place rather than all at once
            (Std.Format.joinSep · ("," ++ Std.Format.line)) <|
            (List.finRange n).map fun j => _root_.repr (f i j)

@[simp]
/-
**Matrix.cons_val'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) : vecCons v B i j = v
ecCons (v j) (fun i => B i j) i
参数：v : n' -> α；B : Fin m -> n' -> α；i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem cons_val' (v : n' → α) (B : Fin m → n' → α) (i j) :
    vecCons v B i j = vecCons (v j) (fun i => B i j) i := by refine Fin.cases ?_ ?_ i <;> simp

@[simp]
/-
**Matrix.head_val'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：head_val' (B : Fin m.succ -> n' -> α) (j : n') : (vecHead fun i => B i j) 
= vecHead B j
参数：B : Fin m.succ -> n' -> α；j : n'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_val' (B : Fin m.succ → n' → α) (j : n') : (vecHead fun i => B i j) = vecHead B j :=
  rfl

@[simp]
/-
**Matrix.tail_val'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：tail_val' (B : Fin m.succ -> n' -> α) (j : n') : (vecTail fun i => B i j) 
= fun i => vecTail B i j
参数：B : Fin m.succ -> n' -> α；j : n'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_val' (B : Fin m.succ → n' → α) (j : n') :
    (vecTail fun i => B i j) = fun i => vecTail B i j := rfl

section DotProduct

variable [AddCommMonoid α] [Mul α]

@[simp]
/-
**Matrix.dotProduct_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：dotProduct_of_isEmpty [Fintype n'] [IsEmpty n'] (v w : n' -> α) : v ⬝ᵥ w =
 0
参数：v w : n' -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_of_isEmpty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst
 : AddCommMonoid M] [IsEmpty ι] (s : Finset ι), ∑ i ∈ s, f i = 0
-/
theorem dotProduct_of_isEmpty [Fintype n'] [IsEmpty n'] (v w : n' → α) : v ⬝ᵥ w = 0 :=
  Finset.sum_of_isEmpty _

@[simp]
/-
**Matrix.cons_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_dotProduct (x : α) (v : Fin n -> α) (w : Fin n.succ -> α) : vecCons x
 v ⬝ᵥ w = x * vecHead w + v ⬝ᵥ vecTail w
参数：x : α；v : Fin n -> α；w : Fin n.succ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_dotProduct (x : α) (v : Fin n → α) (w : Fin n.succ → α) :
    vecCons x v ⬝ᵥ w = x * vecHead w + v ⬝ᵥ vecTail w := by
  simp [dotProduct, Fin.sum_univ_succ, vecHead, vecTail]

@[simp]
/-
**Matrix.dotProduct_cons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：dotProduct_cons (v : Fin n.succ -> α) (x : α) (w : Fin n -> α) : v ⬝ᵥ vecC
ons x w = vecHead v * x + vecTail v ⬝ᵥ w
参数：v : Fin n.succ -> α；x : α；w : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dotProduct_cons (v : Fin n.succ → α) (x : α) (w : Fin n → α) :
    v ⬝ᵥ vecCons x w = vecHead v * x + vecTail v ⬝ᵥ w := by
  simp [dotProduct, Fin.sum_univ_succ, vecHead, vecTail]
/-
**Matrix.cons_dotProduct_cons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_dotProduct_cons (x : α) (v : Fin n -> α) (y : α) (w : Fin n -> α) : v
ecCons x v ⬝ᵥ vecCons y w = x * y + v ⬝ᵥ w
参数：x : α；v : Fin n -> α；y : α；w : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.dotProduct_cons`：dotProduct_cons (v : Fin n.succ -> α) (x : α) (w
 : Fin n -> α) : v ⬝ᵥ vecCons x w = vecHead v * x + vecTail v ⬝ᵥ w
· 使用定理 `Matrix.tail_cons`：tail_cons (x : α) (u : Fin m -> α) : vecTail (vecCons 
x u) = u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_dotProduct_cons (x : α) (v : Fin n → α) (y : α) (w : Fin n → α) :
    vecCons x v ⬝ᵥ vecCons y w = x * y + v ⬝ᵥ w := by simp

end DotProduct

section Diagonal
variable [Zero α]

/-
**Matrix.diagonal_fin_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_fin_one (d : Fin 1 -> α) : diagonal d = !![d 0]
参数：d : Fin 1 -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagonal_fin_one (d : Fin 1 → α) : diagonal d = !![d 0] := by
  simp [← Matrix.ext_iff]
/-
**Matrix.diagonal_vec1** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_vec1 (a : α) : diagonal ![a] = !![a]
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_fin_one`：diagonal_fin_one (d : Fin 1 -> α) : diagonal d 
= !![d 0]
-/
theorem diagonal_vec1 (a : α) : diagonal ![a] = !![a] :=
  diagonal_fin_one ![a]
/-
**Matrix.diagonal_fin_two** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_fin_two (d : Fin 2 -> α) : diagonal d = !![d 0, 0; 0, d 1]
参数：d : Fin 2 -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem diagonal_fin_two (d : Fin 2 → α) : diagonal d = !![d 0, 0; 0, d 1] := by
  simp [← Matrix.ext_iff]
/-
**Matrix.diagonal_vec2** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_vec2 (a b : α) : diagonal ![a, b] = !![a, 0; 0, b]
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_fin_two`：diagonal_fin_two (d : Fin 2 -> α) : diagonal d 
= !![d 0, 0; 0, d 1]
-/
theorem diagonal_vec2 (a b : α) : diagonal ![a, b] = !![a, 0; 0, b] :=
  diagonal_fin_two ![a, b]
/-
**Matrix.diagonal_fin_three** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_fin_three (d : Fin 3 -> α) : diagonal d = !![d 0, 0, 0; 0, d 1, 0
; 0, 0, d 2]
参数：d : Fin 3 -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem diagonal_fin_three (d : Fin 3 → α) :
    diagonal d = !![d 0, 0, 0; 0, d 1, 0; 0, 0, d 2] := by
  simp [← Matrix.ext_iff, Fin.forall_fin_succ]
/-
**Matrix.diagonal_vec3** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_vec3 (a b c : α) : diagonal ![a, b, c] = !![a, 0, 0; 0, b, 0; 0, 
0, c]
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_fin_three`：diagonal_fin_three (d : Fin 3 -> α) : diagona
l d = !![d 0, 0, 0; 0, d 1, 0; 0, 0, d 2]
-/
theorem diagonal_vec3 (a b c : α) :
    diagonal ![a, b, c] = !![a, 0, 0; 0, b, 0; 0, 0, c] :=
  diagonal_fin_three ![a, b, c]

end Diagonal

section ColRow

variable {ι : Type*}

@[simp]
/-
**Matrix.replicateCol_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateCol_empty (v : Fin 0 -> α) : replicateCol ι v = of vecEmpty
参数：v : Fin 0 -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
-/
theorem replicateCol_empty (v : Fin 0 → α) : replicateCol ι v = of vecEmpty :=
  empty_eq _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Matrix.replicateCol_cons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateCol_cons (x : α) (u : Fin m -> α) : replicateCol ι (vecCons x u) 
= of (vecCons (fun _ => x) (replicateCol ι u))
参数：x : α；u : Fin m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem replicateCol_cons (x : α) (u : Fin m → α) :
    replicateCol ι (vecCons x u) = of (vecCons (fun _ => x) (replicateCol ι u)) := by
  ext i j
  refine Fin.cases ?_ ?_ i <;> simp

@[simp]
/-
**Matrix.replicateRow_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateRow_empty : replicateRow ι (vecEmpty : Fin 0 -> α) = of fun _ => 
vecEmpty
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem replicateRow_empty : replicateRow ι (vecEmpty : Fin 0 → α) = of fun _ => vecEmpty := rfl

@[simp]
/-
**Matrix.replicateRow_cons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：replicateRow_cons (x : α) (u : Fin m -> α) : replicateRow ι (vecCons x u) 
= of fun _ => vecCons x u
参数：x : α；u : Fin m -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem replicateRow_cons (x : α) (u : Fin m → α) :
    replicateRow ι (vecCons x u) = of fun _ => vecCons x u :=
  rfl

end ColRow

section Transpose

@[simp]
/-
**Matrix.transpose_empty_rows** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_empty_rows (A : Matrix m' (Fin 0) α) : Aᵀ = of ![]
参数：A : Matrix m' (Fin 0) α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
-/
theorem transpose_empty_rows (A : Matrix m' (Fin 0) α) : Aᵀ = of ![] :=
  empty_eq _

@[simp]
/-
**Matrix.transpose_empty_cols** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_empty_cols (A : Matrix (Fin 0) m' α) : Aᵀ = of fun _ => ![]
参数：A : Matrix (Fin 0) m' α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
-/
theorem transpose_empty_cols (A : Matrix (Fin 0) m' α) : Aᵀ = of fun _ => ![] :=
  funext fun _ => empty_eq _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Matrix.cons_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_transpose (v : n' -> α) (A : Matrix (Fin m) n' α) : (of (vecCons v A)
)ᵀ = of fun i => vecCons (v i) (Aᵀ i)
参数：v : n' -> α；A : Matrix (Fin m) n' α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem cons_transpose (v : n' → α) (A : Matrix (Fin m) n' α) :
    (of (vecCons v A))ᵀ = of fun i => vecCons (v i) (Aᵀ i) := by
  ext i j
  refine Fin.cases ?_ ?_ j <;> simp

@[simp]
/-
**Matrix.head_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：head_transpose (A : Matrix m' (Fin n.succ) α) : vecHead (of.symm Aᵀ) = vec
Head ∘ of.symm A
参数：A : Matrix m' (Fin n.succ) α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem head_transpose (A : Matrix m' (Fin n.succ) α) :
    vecHead (of.symm Aᵀ) = vecHead ∘ of.symm A :=
  rfl

@[simp]
/-
**Matrix.tail_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：tail_transpose (A : Matrix m' (Fin n.succ) α) : vecTail (of.symm Aᵀ) = (ve
cTail ∘ A)ᵀ
参数：A : Matrix m' (Fin n.succ) α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem tail_transpose (A : Matrix m' (Fin n.succ) α) : vecTail (of.symm Aᵀ) = (vecTail ∘ A)ᵀ := by
  ext i j
  rfl

end Transpose

section Mul

variable [NonUnitalNonAssocSemiring α]

@[simp]
/-
**Matrix.empty_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：empty_mul [Fintype n'] (A : Matrix (Fin 0) n' α) (B : Matrix n' o' α) : A 
* B = of ![]
参数：A : Matrix (Fin 0) n' α；B : Matrix n' o' α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
-/
theorem empty_mul [Fintype n'] (A : Matrix (Fin 0) n' α) (B : Matrix n' o' α) : A * B = of ![] :=
  empty_eq _

@[simp]
/-
**Matrix.empty_mul_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：empty_mul_empty (A : Matrix m' (Fin 0) α) (B : Matrix (Fin 0) o' α) : A * 
B = 0
参数：A : Matrix m' (Fin 0) α；B : Matrix (Fin 0) o' α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem empty_mul_empty (A : Matrix m' (Fin 0) α) (B : Matrix (Fin 0) o' α) : A * B = 0 :=
  rfl

@[simp]
/-
**Matrix.mul_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_empty [Fintype n'] (A : Matrix m' n' α) (B : Matrix n' (Fin 0) α) : A 
* B = of fun _ => ![]
参数：A : Matrix m' n' α；B : Matrix n' (Fin 0) α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
-/
theorem mul_empty [Fintype n'] (A : Matrix m' n' α) (B : Matrix n' (Fin 0) α) :
    A * B = of fun _ => ![] :=
  funext fun _ => empty_eq _
/-
**Matrix.mul_val_succ** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_val_succ [Fintype n'] (A : Matrix (Fin m.succ) n' α) (B : Matrix n' o'
 α) (i : Fin m) (j : o') : (A * B) i.succ j = (of (vecTail (of.symm A)) * B) i j
参数：A : Matrix (Fin m.succ) n' α；B : Matrix n' o' α；i : Fin m；j : o'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_val_succ [Fintype n'] (A : Matrix (Fin m.succ) n' α) (B : Matrix n' o' α) (i : Fin m)
    (j : o') : (A * B) i.succ j = (of (vecTail (of.symm A)) * B) i j :=
  rfl

@[simp]
/-
**Matrix.cons_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_mul [Fintype n'] (v : n' -> α) (A : Fin m -> n' -> α) (B : Matrix n' 
o' α) : of (vecCons v A) * B = of (vecCons (v ᵥ* B) (of.symm (of A * B)))
参数：v : n' -> α；A : Fin m -> n' -> α；B : Matrix n' o' α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Matrix.tail_cons`：tail_cons (x : α) (u : Fin m -> α) : vecTail (vecCons 
x u) = u
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem cons_mul [Fintype n'] (v : n' → α) (A : Fin m → n' → α) (B : Matrix n' o' α) :
    of (vecCons v A) * B = of (vecCons (v ᵥ* B) (of.symm (of A * B))) := by
  ext i j
  refine Fin.cases ?_ ?_ i
  · rfl
  simp [mul_val_succ]

end Mul

section VecMul

variable [NonUnitalNonAssocSemiring α]

@[simp]
/-
**Matrix.empty_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：empty_vecMul (v : Fin 0 -> α) (B : Matrix (Fin 0) o' α) : v ᵥ* B = 0
参数：v : Fin 0 -> α；B : Matrix (Fin 0) o' α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem empty_vecMul (v : Fin 0 → α) (B : Matrix (Fin 0) o' α) : v ᵥ* B = 0 :=
  rfl

@[simp]
/-
**Matrix.vecMul_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_empty [Fintype n'] (v : n' -> α) (B : Matrix n' (Fin 0) α) : v ᵥ* B
 = ![]
参数：v : n' -> α；B : Matrix n' (Fin 0) α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
-/
theorem vecMul_empty [Fintype n'] (v : n' → α) (B : Matrix n' (Fin 0) α) : v ᵥ* B = ![] :=
  empty_eq _

@[simp]
/-
**Matrix.cons_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_vecMul (x : α) (v : Fin n -> α) (B : Fin n.succ -> o' -> α) : vecCons
 x v ᵥ* of B = x • vecHead B + v ᵥ* of (vecTail B)
参数：x : α；v : Fin n -> α；B : Fin n.succ -> o' -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_dotProduct`：cons_dotProduct (x : α) (v : Fin n -> α) (w : Fi
n n.succ -> α) : vecCons x v ⬝ᵥ w = x * vecHead w + v ⬝ᵥ vecTail w
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_vecMul (x : α) (v : Fin n → α) (B : Fin n.succ → o' → α) :
    vecCons x v ᵥ* of B = x • vecHead B + v ᵥ* of (vecTail B) := by
  ext i
  simp [vecMul]

@[simp]
/-
**Matrix.vecMul_cons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_cons (v : Fin n.succ -> α) (w : o' -> α) (B : Fin n -> o' -> α) : v
 ᵥ* of (vecCons w B) = vecHead v • w + vecTail v ᵥ* of B
参数：v : Fin n.succ -> α；w : o' -> α；B : Fin n -> o' -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `Matrix.dotProduct_cons`：dotProduct_cons (v : Fin n.succ -> α) (x : α) (w
 : Fin n -> α) : v ⬝ᵥ vecCons x w = vecHead v * x + vecTail v ⬝ᵥ w
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vecMul_cons (v : Fin n.succ → α) (w : o' → α) (B : Fin n → o' → α) :
    v ᵥ* of (vecCons w B) = vecHead v • w + vecTail v ᵥ* of B := by
  ext i
  simp [vecMul]
/-
**Matrix.cons_vecMul_cons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_vecMul_cons (x : α) (v : Fin n -> α) (w : o' -> α) (B : Fin n -> o' -
> α) : vecCons x v ᵥ* of (vecCons w B) = x • w + v ᵥ* of B
参数：x : α；v : Fin n -> α；w : o' -> α；B : Fin n -> o' -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.vecMul_cons`：vecMul_cons (v : Fin n.succ -> α) (w : o' -> α) (B :
 Fin n -> o' -> α) : v ᵥ* of (vecCons w B) = vecHead v • w + vecTail v ᵥ* of B
· 使用定理 `Matrix.tail_cons`：tail_cons (x : α) (u : Fin m -> α) : vecTail (vecCons 
x u) = u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_vecMul_cons (x : α) (v : Fin n → α) (w : o' → α) (B : Fin n → o' → α) :
    vecCons x v ᵥ* of (vecCons w B) = x • w + v ᵥ* of B := by simp

end VecMul

section MulVec

variable [NonUnitalNonAssocSemiring α]

@[simp]
/-
**Matrix.empty_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：empty_mulVec [Fintype n'] (A : Matrix (Fin 0) n' α) (v : n' -> α) : A *ᵥ v
 = ![]
参数：A : Matrix (Fin 0) n' α；v : n' -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
-/
theorem empty_mulVec [Fintype n'] (A : Matrix (Fin 0) n' α) (v : n' → α) : A *ᵥ v = ![] :=
  empty_eq _

@[simp]
/-
**Matrix.mulVec_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_empty (A : Matrix m' (Fin 0) α) (v : Fin 0 -> α) : A *ᵥ v = 0
参数：A : Matrix m' (Fin 0) α；v : Fin 0 -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulVec_empty (A : Matrix m' (Fin 0) α) (v : Fin 0 → α) : A *ᵥ v = 0 :=
  rfl

@[simp]
/-
**Matrix.cons_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_mulVec [Fintype n'] (v : n' -> α) (A : Fin m -> n' -> α) (w : n' -> α
) : (of <| vecCons v A) *ᵥ w = vecCons (v ⬝ᵥ w) (of A *ᵥ w)
参数：v : n' -> α；A : Fin m -> n' -> α；w : n' -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem cons_mulVec [Fintype n'] (v : n' → α) (A : Fin m → n' → α) (w : n' → α) :
    (of <| vecCons v A) *ᵥ w = vecCons (v ⬝ᵥ w) (of A *ᵥ w) := by
  ext i
  refine Fin.cases ?_ ?_ i <;> simp [mulVec]

@[simp]
/-
**Matrix.mulVec_cons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_cons {α} [NonUnitalCommSemiring α] (A : m' -> Fin n.succ -> α) (x :
 α) (v : Fin n -> α) : (of A) *ᵥ (vecCons x v) = x • vecHead ∘ A + (of (vecTail 
∘ A)) *ᵥ v
参数：A : m' -> Fin n.succ -> α；x : α；v : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.dotProduct_cons`：dotProduct_cons (v : Fin n.succ -> α) (x : α) (w
 : Fin n -> α) : v ⬝ᵥ vecCons x w = vecHead v * x + vecTail v ⬝ᵥ w
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulVec_cons {α} [NonUnitalCommSemiring α] (A : m' → Fin n.succ → α) (x : α)
    (v : Fin n → α) : (of A) *ᵥ (vecCons x v) = x • vecHead ∘ A + (of (vecTail ∘ A)) *ᵥ v := by
  ext i
  simp [mulVec, mul_comm]

end MulVec

section VecMulVec

variable [NonUnitalNonAssocSemiring α]

@[simp]
/-
**Matrix.empty_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：empty_vecMulVec (v : Fin 0 -> α) (w : n' -> α) : vecMulVec v w = of ![]
参数：v : Fin 0 -> α；w : n' -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
-/
theorem empty_vecMulVec (v : Fin 0 → α) (w : n' → α) : vecMulVec v w = of ![] :=
  empty_eq _

@[simp]
/-
**Matrix.vecMulVec_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMulVec_empty (v : m' -> α) (w : Fin 0 -> α) : vecMulVec v w = of fun _ 
=> ![]
参数：v : m' -> α；w : Fin 0 -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
-/
theorem vecMulVec_empty (v : m' → α) (w : Fin 0 → α) : vecMulVec v w = of fun _ => ![] :=
  funext fun _ => empty_eq _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Matrix.cons_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_vecMulVec (x : α) (v : Fin m -> α) (w : n' -> α) : vecMulVec (vecCons
 x v) w = vecCons (x • w) (vecMulVec v w)
参数：x : α；v : Fin m -> α；w : n' -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem cons_vecMulVec (x : α) (v : Fin m → α) (w : n' → α) :
    vecMulVec (vecCons x v) w = vecCons (x • w) (vecMulVec v w) := by
  ext i
  refine Fin.cases ?_ ?_ i <;> simp [vecMulVec]

@[simp]
/-
**Matrix.vecMulVec_cons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMulVec_cons (v : m' -> α) (x : α) (w : Fin n -> α) : vecMulVec v (vecCo
ns x w) = of fun i => v i • vecCons x w
参数：v : m' -> α；x : α；w : Fin n -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vecMulVec_cons (v : m' → α) (x : α) (w : Fin n → α) :
    vecMulVec v (vecCons x w) = of fun i => v i • vecCons x w := rfl

end VecMulVec

section SMul

variable [NonUnitalNonAssocSemiring α]

/-
**Matrix.smul_mat_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：smul_mat_empty {m' : Type*} (x : α) (A : Fin 0 -> m' -> α) : x • A = ![]
参数：x : α；A : Fin 0 -> m' -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
-/
theorem smul_mat_empty {m' : Type*} (x : α) (A : Fin 0 → m' → α) : x • A = ![] :=
  empty_eq _

end SMul

section Submatrix

@[simp]
/-
**Matrix.submatrix_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_empty (A : Matrix m' n' α) (row : Fin 0 -> m') (col : o' -> n') 
: submatrix A row col = of ![]
参数：A : Matrix m' n' α；row : Fin 0 -> m'；col : o' -> n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
-/
theorem submatrix_empty (A : Matrix m' n' α) (row : Fin 0 → m') (col : o' → n') :
    submatrix A row col = of ![] :=
  empty_eq _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Matrix.submatrix_cons_row** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_cons_row (A : Matrix m' n' α) (i : m') (row : Fin m -> m') (col 
: o' -> n') : submatrix A (vecCons i row) col = vecCons (fun j => A i (col j)) (
submatrix A row col)
参数：A : Matrix m' n' α；i : m'；row : Fin m -> m'；col : o' -> n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem submatrix_cons_row (A : Matrix m' n' α) (i : m') (row : Fin m → m') (col : o' → n') :
    submatrix A (vecCons i row) col = vecCons (fun j => A i (col j)) (submatrix A row col) := by
  ext i j
  refine Fin.cases ?_ ?_ i <;> simp [submatrix]

/-- Updating a row then removing it is the same as removing it. -/
@[simp]
/-
**Matrix.submatrix_updateRow_succAbove** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_updateRow_succAbove (A : Matrix (Fin m.succ) n' α) (v : n' -> α)
 (f : o' -> n') (i : Fin m.succ) : (A.updateRow i v).submatrix i.succAbove f = A
.submatrix i.succAbove f
参数：A : Matrix (Fin m.succ) n' α；v : n' -> α；f : o' -> n'；i : Fin m.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Matrix.updateRow_ne`：updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' !=
 i) : updateRow M i b i' = M i'
· 使用引理 `Fin.succAbove_ne`：succAbove_ne (p : Fin (n + 1)) (i : Fin n) : p.succAbo
ve i != p

--- 原说明 ---
Updating a row then removing it is the same as removing it.
-/
theorem submatrix_updateRow_succAbove (A : Matrix (Fin m.succ) n' α) (v : n' → α) (f : o' → n')
    (i : Fin m.succ) : (A.updateRow i v).submatrix i.succAbove f = A.submatrix i.succAbove f :=
  ext fun r s => (congr_fun (updateRow_ne (Fin.succAbove_ne i r) : _ = A _) (f s) :)

/-- Updating a column then removing it is the same as removing it. -/
@[simp]
/-
**Matrix.submatrix_updateCol_succAbove** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_updateCol_succAbove (A : Matrix m' (Fin n.succ) α) (v : m' -> α)
 (f : o' -> m') (i : Fin n.succ) : (A.updateCol i v).submatrix f i.succAbove = A
.submatrix f i.succAbove
参数：A : Matrix m' (Fin n.succ) α；v : m' -> α；f : o' -> m'；i : Fin n.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Matrix.updateCol_ne`：updateCol_ne [DecidableEq n] {j' : n} (j_ne : j' !=
 j) : updateCol M j c i j' = M i j'
· 使用引理 `Fin.succAbove_ne`：succAbove_ne (p : Fin (n + 1)) (i : Fin n) : p.succAbo
ve i != p

--- 原说明 ---
Updating a column then removing it is the same as removing it.
-/
theorem submatrix_updateCol_succAbove (A : Matrix m' (Fin n.succ) α) (v : m' → α) (f : o' → m')
    (i : Fin n.succ) : (A.updateCol i v).submatrix f i.succAbove = A.submatrix f i.succAbove :=
  ext fun _r s => updateCol_ne (Fin.succAbove_ne i s)

end Submatrix

section Vec2AndVec3

section One

variable [Zero α] [One α]

/-
**Matrix.one_fin_two** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_fin_two : (1 : Matrix (Fin 2) (Fin 2) α) = !![1, 0; 0, 1]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem one_fin_two : (1 : Matrix (Fin 2) (Fin 2) α) = !![1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
/-
**Matrix.one_fin_three** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_fin_three : (1 : Matrix (Fin 3) (Fin 3) α) = !![1, 0, 0; 0, 1, 0; 0, 0
, 1]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem one_fin_three : (1 : Matrix (Fin 3) (Fin 3) α) = !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end One

section AddMonoidWithOne
variable [AddMonoidWithOne α]

/-
**Matrix.natCast_fin_two** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：natCast_fin_two (n : Nat) : (n : Matrix (Fin 2) (Fin 2) α) = !![↑n, 0; 0, 
↑n]
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem natCast_fin_two (n : ℕ) : (n : Matrix (Fin 2) (Fin 2) α) = !![↑n, 0; 0, ↑n] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
/-
**Matrix.natCast_fin_three** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：natCast_fin_three (n : Nat) : (n : Matrix (Fin 3) (Fin 3) α) = !![↑n, 0, 0
; 0, ↑n, 0; 0, 0, ↑n]
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem natCast_fin_three (n : ℕ) :
    (n : Matrix (Fin 3) (Fin 3) α) = !![↑n, 0, 0; 0, ↑n, 0; 0, 0, ↑n] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
/-
**Matrix.ofNat_fin_two** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ofNat_fin_two (n : Nat) [n.AtLeastTwo] : (ofNat(n) : Matrix (Fin 2) (Fin 2
) α) = !![ofNat(n), 0; 0, ofNat(n)]
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.natCast_fin_two`：natCast_fin_two (n : Nat) : (n : Matrix (Fin 2) 
(Fin 2) α) = !![↑n, 0; 0, ↑n]
-/
theorem ofNat_fin_two (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : Matrix (Fin 2) (Fin 2) α) =
      !![ofNat(n), 0; 0, ofNat(n)] :=
  natCast_fin_two _
/-
**Matrix.ofNat_fin_three** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ofNat_fin_three (n : Nat) [n.AtLeastTwo] : (ofNat(n) : Matrix (Fin 3) (Fin
 3) α) = !![ofNat(n), 0, 0; 0, ofNat(n), 0; 0, 0, ofNat(n)]
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.natCast_fin_three`：natCast_fin_three (n : Nat) : (n : Matrix (Fin
 3) (Fin 3) α) = !![↑n, 0, 0; 0, ↑n, 0; 0, 0, ↑n]
-/
theorem ofNat_fin_three (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : Matrix (Fin 3) (Fin 3) α) =
      !![ofNat(n), 0, 0; 0, ofNat(n), 0; 0, 0, ofNat(n)] :=
  natCast_fin_three _

end AddMonoidWithOne

/-
**Matrix.eta_fin_two** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：eta_fin_two (A : Matrix (Fin 2) (Fin 2) α) : A = !![A 0 0, A 0 1; A 1 0, A
 1 1]
参数：A : Matrix (Fin 2) (Fin 2) α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem eta_fin_two (A : Matrix (Fin 2) (Fin 2) α) : A = !![A 0 0, A 0 1; A 1 0, A 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
/-
**Matrix.eta_fin_three** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：eta_fin_three (A : Matrix (Fin 3) (Fin 3) α) : A = !![A 0 0, A 0 1, A 0 2;
 A 1 0, A 1 1, A 1 2; A 2 0, A 2 1, A 2 2]
参数：A : Matrix (Fin 3) (Fin 3) α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem eta_fin_three (A : Matrix (Fin 3) (Fin 3) α) :
    A = !![A 0 0, A 0 1, A 0 2;
           A 1 0, A 1 1, A 1 2;
           A 2 0, A 2 1, A 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
/-
**Matrix.mul_fin_two** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_fin_two [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α
) : !![a₁₁, a₁₂; a₂₁, a₂₂] * !![b₁₁, b₁₂; b₂₁, b₂₂] = !![a₁₁ * b₁₁ + a₁₂ * b₂₁, 
a₁₁ * b₁₂ + a₁₂ * b₂₂; a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂]
参数：a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem mul_fin_two [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
    !![a₁₁, a₁₂;
       a₂₁, a₂₂] * !![b₁₁, b₁₂;
                      b₂₁, b₂₂] = !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
                                     a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

set_option linter.style.whitespace false in -- Preserve the formatting of the matrices.
/-
**Matrix.mul_fin_three** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_fin_three [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a
₃₃ b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ : α) : !![a₁₁, a₁₂, a₁₃; a₂₁, a₂₂, a₂₃; a
₃₁, a₃₂, a₃₃] * !![b₁₁, b₁₂, b₁₃; b₂₁, b₂₂, b₂₃; b₃₁, b₃₂, b₃₃] = !![a₁₁*b₁₁ + a
₁₂*b₂₁ + a₁₃*b₃₁, a₁₁*b₁₂ + a₁₂*b₂₂ + a₁₃*b₃₂, a₁₁*b₁₃ + a₁₂*b₂₃ + a₁₃*b₃₃; a₂₁*
b₁₁ + a₂₂*b₂₁ + a₂₃*b₃₁, a₂₁*b₁₂ + a₂₂*b₂₂ + a₂₃*b₃₂, a₂₁*b₁₃ + a₂₂*b₂₃ + a₂₃*b₃
₃; a₃₁*b₁₁ + a₃₂*b₂₁ + a₃₃*b₃₁, a₃₁*b₁₂ + a₃₂*b₂₂ + a₃₃*b₃₂, a₃₁*b₁₃ + a₃₂*b₂₃ +
 a₃₃*b₃₃]
参数：a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem mul_fin_three [AddCommMonoid α] [Mul α]
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ : α) :
    !![a₁₁, a₁₂, a₁₃;
       a₂₁, a₂₂, a₂₃;
       a₃₁, a₃₂, a₃₃] * !![b₁₁, b₁₂, b₁₃;
                           b₂₁, b₂₂, b₂₃;
                           b₃₁, b₃₂, b₃₃] =
    !![a₁₁*b₁₁ + a₁₂*b₂₁ + a₁₃*b₃₁, a₁₁*b₁₂ + a₁₂*b₂₂ + a₁₃*b₃₂, a₁₁*b₁₃ + a₁₂*b₂₃ + a₁₃*b₃₃;
       a₂₁*b₁₁ + a₂₂*b₂₁ + a₂₃*b₃₁, a₂₁*b₁₂ + a₂₂*b₂₂ + a₂₃*b₃₂, a₂₁*b₁₃ + a₂₂*b₂₃ + a₂₃*b₃₃;
       a₃₁*b₁₁ + a₃₂*b₂₁ + a₃₃*b₃₁, a₃₁*b₁₂ + a₃₂*b₂₂ + a₃₃*b₃₂, a₃₁*b₁₃ + a₃₂*b₂₃ + a₃₃*b₃₃] := by
  ext i j
  fin_cases i <;> fin_cases j
    <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, ← add_assoc]
/-
**Matrix.vec2_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec2_eq {a₀ a₁ b₀ b₁ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) : ![a₀, a₁] = ![b₀
, b₁]
参数：h₀ : a₀ = b₀；h₁ : a₁ = b₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vec2_eq {a₀ a₁ b₀ b₁ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) : ![a₀, a₁] = ![b₀, b₁] := by
  simp [h₀, h₁]
/-
**Matrix.vec3_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec3_eq {a₀ a₁ a₂ b₀ b₁ b₂ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b
₂) : ![a₀, a₁, a₂] = ![b₀, b₁, b₂]
参数：h₀ : a₀ = b₀；h₁ : a₁ = b₁；h₂ : a₂ = b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vec3_eq {a₀ a₁ a₂ b₀ b₁ b₂ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) :
    ![a₀, a₁, a₂] = ![b₀, b₁, b₂] := by
  simp [h₀, h₁, h₂]
/-
**Matrix.vec2_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec2_add [Add α] (a₀ a₁ b₀ b₁ : α) : ![a₀, a₁] + ![b₀, b₁] = ![a₀ + b₀, a₁
 + b₁]
参数：a₀ a₁ b₀ b₁ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.add_cons`：∀ {α : Type u_1} {n : ℕ} [inst : Add α] (v : Fin n.succ
 → α) (y : α) (w : Fin n → α),   v + Matrix.vecCons y w = Matrix.vecCons (Matrix
.vecH…
· 使用定理 `Matrix.tail_cons`：tail_cons (x : α) (u : Fin m -> α) : vecTail (vecCons 
x u) = u
· 使用定理 `Matrix.empty_add_empty`：∀ {α : Type u_1} [inst : Add α] (v w : Fin 0 → α
), v + w = ![]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vec2_add [Add α] (a₀ a₁ b₀ b₁ : α) : ![a₀, a₁] + ![b₀, b₁] = ![a₀ + b₀, a₁ + b₁] := by
  simp
/-
**Matrix.vec3_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec3_add [Add α] (a₀ a₁ a₂ b₀ b₁ b₂ : α) : ![a₀, a₁, a₂] + ![b₀, b₁, b₂] =
 ![a₀ + b₀, a₁ + b₁, a₂ + b₂]
参数：a₀ a₁ a₂ b₀ b₁ b₂ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.add_cons`：∀ {α : Type u_1} {n : ℕ} [inst : Add α] (v : Fin n.succ
 → α) (y : α) (w : Fin n → α),   v + Matrix.vecCons y w = Matrix.vecCons (Matrix
.vecH…
· 使用定理 `Matrix.tail_cons`：tail_cons (x : α) (u : Fin m -> α) : vecTail (vecCons 
x u) = u
· 使用定理 `Matrix.empty_add_empty`：∀ {α : Type u_1} [inst : Add α] (v w : Fin 0 → α
), v + w = ![]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vec3_add [Add α] (a₀ a₁ a₂ b₀ b₁ b₂ : α) :
    ![a₀, a₁, a₂] + ![b₀, b₁, b₂] = ![a₀ + b₀, a₁ + b₁, a₂ + b₂] := by
  simp
/-
**Matrix.smul_vec2** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：smul_vec2 {R : Type*} [SMul R α] (x : R) (a₀ a₁ : α) : x • ![a₀, a₁] = ![x
 • a₀, x • a₁]
参数：x : R；a₀ a₁ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.smul_cons`：∀ {α : Type u_1} {M : Type u_2} {n : ℕ} [inst : SMul M
 α] (x : M) (y : α) (v : Fin n → α),   x • Matrix.vecCons y v = Matrix.vecCons (
x • y)…
· 使用定理 `Matrix.smul_empty`：∀ {α : Type u_1} {M : Type u_2} [inst : SMul M α] (x 
: M) (v : Fin 0 → α), x • v = ![]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_vec2 {R : Type*} [SMul R α] (x : R) (a₀ a₁ : α) :
    x • ![a₀, a₁] = ![x • a₀, x • a₁] := by
  simp
/-
**Matrix.smul_vec3** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：smul_vec3 {R : Type*} [SMul R α] (x : R) (a₀ a₁ a₂ : α) : x • ![a₀, a₁, a₂
] = ![x • a₀, x • a₁, x • a₂]
参数：x : R；a₀ a₁ a₂ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.smul_cons`：∀ {α : Type u_1} {M : Type u_2} {n : ℕ} [inst : SMul M
 α] (x : M) (y : α) (v : Fin n → α),   x • Matrix.vecCons y v = Matrix.vecCons (
x • y)…
· 使用定理 `Matrix.smul_empty`：∀ {α : Type u_1} {M : Type u_2} [inst : SMul M α] (x 
: M) (v : Fin 0 → α), x • v = ![]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_vec3 {R : Type*} [SMul R α] (x : R) (a₀ a₁ a₂ : α) :
    x • ![a₀, a₁, a₂] = ![x • a₀, x • a₁, x • a₂] := by
  simp

variable [AddCommMonoid α] [Mul α]
/-
**Matrix.vec2_dotProduct'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec2_dotProduct' {a₀ a₁ b₀ b₁ : α} : ![a₀, a₁] ⬝ᵥ ![b₀, b₁] = a₀ * b₀ + a₁
 * b₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.dotProduct_cons`：dotProduct_cons (v : Fin n.succ -> α) (x : α) (w
 : Fin n -> α) : v ⬝ᵥ vecCons x w = vecHead v * x + vecTail v ⬝ᵥ w
· 使用定理 `Matrix.tail_cons`：tail_cons (x : α) (u : Fin m -> α) : vecTail (vecCons 
x u) = u
· 使用定理 `Matrix.dotProduct_of_isEmpty`：dotProduct_of_isEmpty [Fintype n'] [IsEmpt
y n'] (v w : n' -> α) : v ⬝ᵥ w = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vec2_dotProduct' {a₀ a₁ b₀ b₁ : α} : ![a₀, a₁] ⬝ᵥ ![b₀, b₁] = a₀ * b₀ + a₁ * b₁ := by
  simp

@[simp]
/-
**Matrix.vec2_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec2_dotProduct (v w : Fin 2 -> α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1
参数：v w : Fin 2 -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.vec2_dotProduct'`：vec2_dotProduct' {a₀ a₁ b₀ b₁ : α} : ![a₀, a₁] 
⬝ᵥ ![b₀, b₁] = a₀ * b₀ + a₁ * b₁
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
-/
theorem vec2_dotProduct (v w : Fin 2 → α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 :=
  vec2_dotProduct'
/-
**Matrix.vec3_dotProduct'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec3_dotProduct' {a₀ a₁ a₂ b₀ b₁ b₂ : α} : ![a₀, a₁, a₂] ⬝ᵥ ![b₀, b₁, b₂] 
= a₀ * b₀ + a₁ * b₁ + a₂ * b₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.dotProduct_cons`：dotProduct_cons (v : Fin n.succ -> α) (x : α) (w
 : Fin n -> α) : v ⬝ᵥ vecCons x w = vecHead v * x + vecTail v ⬝ᵥ w
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.tail_cons`：tail_cons (x : α) (u : Fin m -> α) : vecTail (vecCons 
x u) = u
· 使用定理 `Matrix.dotProduct_of_isEmpty`：dotProduct_of_isEmpty [Fintype n'] [IsEmpt
y n'] (v w : n' -> α) : v ⬝ᵥ w = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vec3_dotProduct' {a₀ a₁ a₂ b₀ b₁ b₂ : α} :
    ![a₀, a₁, a₂] ⬝ᵥ ![b₀, b₁, b₂] = a₀ * b₀ + a₁ * b₁ + a₂ * b₂ := by
  simp [add_assoc]

-- This is not tagged `@[simp]` because it does not mesh well with simp lemmas for
-- dot and cross products in dimension 3.
/-
**Matrix.vec3_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec3_dotProduct (v w : Fin 3 -> α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 + v 2 
* w 2
参数：v w : Fin 3 -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.vec3_dotProduct'`：vec3_dotProduct' {a₀ a₁ a₂ b₀ b₁ b₂ : α} : ![a₀
, a₁, a₂] ⬝ᵥ ![b₀, b₁, b₂] = a₀ * b₀ + a₁ * b₁ + a₂ * b₂
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
-/
theorem vec3_dotProduct (v w : Fin 3 → α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 :=
  vec3_dotProduct'

end Vec2AndVec3

end Matrix

@[simp]
/-
**injective_pair_iff_ne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：injective_pair_iff_ne {α : Type*} {x y : α} : Function.Injective ![x, y] ↔
 x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Fin.zero_ne_one`：∀ {n : ℕ}, 0 ≠ 1
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
lemma injective_pair_iff_ne {α : Type*} {x y : α} :
    Function.Injective ![x, y] ↔ x ≠ y := by
  refine ⟨fun h ↦ ?_, fun h a b h' ↦ ?_⟩
  · simpa using h.ne Fin.zero_ne_one
  · fin_cases a <;> fin_cases b <;> aesop
