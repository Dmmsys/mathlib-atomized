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

variable {α : Type u} {o n m : Nat} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

open Matrix

section toExpr

open Lean Qq

open Qq in
/-- `Matrix.mkLiteralQ !![a, b; c, d]` produces the term `q(!![$a, $b; $c, $d])`. -/
meta def mkLiteralQ {u : Level} {α : Q(Type u)} {m n : Nat} (elems : Matrix (Fin m) (Fin n) Q($α)) :
    Q(Matrix (Fin $m) (Fin $n) $α) :=
  let elems := PiFin.mkLiteralQ (α := q(Fin $n -> $α)) fun i => PiFin.mkLiteralQ fun j => elems i j
  q(Matrix.of $elems)

/-- Matrices can be reflected whenever their entries can. We insert a `Matrix.of` to
prevent immediate decay to a function. -/
protected meta instance toExpr [ToLevel.{u}] [ToLevel.{uₘ}] [ToLevel.{uₙ}]
    [Lean.ToExpr α] [Lean.ToExpr m'] [Lean.ToExpr n'] [Lean.ToExpr (m' -> n' -> α)] :
    Lean.ToExpr (Matrix m' n' α) :=
  have eα : Q(Type $(toLevel.{u})) := toTypeExpr α
  have em' : Q(Type $(toLevel.{uₘ})) := toTypeExpr m'
  have en' : Q(Type $(toLevel.{uₙ})) := toTypeExpr n'
  { toTypeExpr :=
    q(Matrix $eα $em' $en')
    toExpr := fun M =>
      have eM : Q($em' -> $en' -> $eα) := toExpr (show m' -> n' -> α from M)
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
meta def delabMatrixNotation : Delab := whenNotPPOption getPPExplicit
whenPPOption getPPNotation
  withOverApp 6 do
    let mkApp3 (.const ``Matrix.of _) (.app (.const ``Fin _) em) (.app (.const ``Fin _) en) _ :=
      (← getExpr).appFn!.appArg! | failure
    let some m ← withNatValue em (pure ∘ some) | failure
    let some n ← withNatValue en (pure ∘ some) | failure
    withAppArg do
      if m = 0 then
guard (← getExpr).isAppOfArity ``vecEmpty 1
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

variable (a b : Nat)

/--
Instance `repr` / 实例 `repr`

English:
instance repr
  signature: [Repr α]
  body: (Std.Format.bracket "!![" · "]")
(Std.Format.joinSep · (";" ++ Std.Format.line))
        (List.finRange m).map fun i =>
Std.Format.fill -- wrap line in a single place rather than all at once
(Std.Format.joinSep · ("," ++ Std.Format.line))
            (List.finRange n).map fun j => _root_.repr (f i j

中文:
实例 repr
  签名: [Repr α]
  定义体: (Std.Format.bracket "!![" · "]")
(Std.Format.joinSep · (";" ++ Std.Format.line))
        (List.finRange m).map fun i =>
Std.Format.fill -- wrap line in a single place rather than all at once
(Std.Format.joinSep · ("," ++ Std.Format.line))
            (List.finRange n).map fun j => _root_.repr (f i j

Depends on / 依赖: Format, List.finRange, Std.Format.bracket, Std.Format.fill, Std.Format.joinSep, Std.Format.line, _root_, _root_.repr, bracket, finRange, joinSep, rather, single
-/
instance repr [Repr α] : Repr (Matrix (Fin m) (Fin n) α) where
  reprPrec f _p :=
(Std.Format.bracket "!![" · "]")
(Std.Format.joinSep · (";" ++ Std.Format.line))
        (List.finRange m).map fun i =>
Std.Format.fill -- wrap line in a single place rather than all at once
(Std.Format.joinSep · ("," ++ Std.Format.line))
            (List.finRange n).map fun j => _root_.repr (f i j)

@[simp]
/--
theorem `cons_val'` / 定理 `cons_val'`

English:
theorem cons_val'
  given: (v : n' -> α) (B : Fin m -> n' -> α) (i j)
  proof: by refine Fin.cases ?_ ?_ i <;> simp

@[simp]

中文:
定理 cons_val'
  条件: (v : n' -> α) (B : 有限集 m -> n' -> α) (i j)
  证明: by refine Fin.cases ?_ ?_ i <;> simp

@[simp]

Depends on / 依赖: Fin.cases
-/
theorem cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
    vecCons v B i j = vecCons (v j) (fun i => B i j) i := by refine Fin.cases ?_ ?_ i <;> simp

@[simp]
/--
theorem `head_val'` / 定理 `head_val'`

English:
theorem head_val'
  given: (B : Fin m.succ -> n' -> α) (j : n')
  statement: (vecHead fun i => B i j) = vecHead B j
  proof: rfl

@[simp]

中文:
定理 head_val'
  条件: (B : 有限集 m.succ -> n' -> α) (j : n')
  结论: (vecHead fun i => B i j) = vecHead B j
  证明: rfl

@[simp]
-/
theorem head_val' (B : Fin m.succ -> n' -> α) (j : n') : (vecHead fun i => B i j) = vecHead B j :=
  rfl

@[simp]
/--
theorem `tail_val'` / 定理 `tail_val'`

English:
theorem tail_val'
  given: (B : Fin m.succ -> n' -> α) (j : n')
  proof: rfl

中文:
定理 tail_val'
  条件: (B : 有限集 m.succ -> n' -> α) (j : n')
  证明: rfl
-/
theorem tail_val' (B : Fin m.succ -> n' -> α) (j : n') :
    (vecTail fun i => B i j) = fun i => vecTail B i j := rfl

section DotProduct

variable [AddCommMonoid α] [Mul α]

@[simp]
/--
theorem `dotProduct_of_isEmpty` / 定理 `dotProduct_of_isEmpty`

English:
theorem dotProduct_of_isEmpty
  given: [Fintype n'] [IsEmpty n'] (v w : n' -> α)
  statement: v ⬝ᵥ w = 0
  proof: Finset.sum_of_isEmpty _

@[simp]

中文:
定理 dotProduct_of_isEmpty
  条件: [有限类型 n'] [是空 n'] (v w : n' -> α)
  结论: v ⬝ᵥ w = 0
  证明: Finset.sum_of_isEmpty _

@[simp]

Depends on / 依赖: Finset, Finset.sum_of_isEmpty, sum_of_isEmpty
-/
theorem dotProduct_of_isEmpty [Fintype n'] [IsEmpty n'] (v w : n' -> α) : v ⬝ᵥ w = 0 :=
  Finset.sum_of_isEmpty _

@[simp]
/--
theorem `cons_dotProduct` / 定理 `cons_dotProduct`

English:
theorem cons_dotProduct
  given: (x : α) (v : Fin n -> α) (w : Fin n.succ -> α)
  proof: by
  simp [dotProduct, Fin.sum_univ_succ, vecHead, vecTail]

@[simp]

中文:
定理 cons_dotProduct
  条件: (x : α) (v : 有限集 n -> α) (w : 有限集 n.succ -> α)
  证明: by
  simp [dotProduct, Fin.sum_univ_succ, vecHead, vecTail]

@[simp]

Depends on / 依赖: Fin.sum_univ_succ, dotProduct, sum_univ_succ, vecHead, vecTail
-/
theorem cons_dotProduct (x : α) (v : Fin n -> α) (w : Fin n.succ -> α) :
    vecCons x v ⬝ᵥ w = x * vecHead w + v ⬝ᵥ vecTail w := by
  simp [dotProduct, Fin.sum_univ_succ, vecHead, vecTail]

@[simp]
/--
theorem `dotProduct_cons` / 定理 `dotProduct_cons`

English:
theorem dotProduct_cons
  given: (v : Fin n.succ -> α) (x : α) (w : Fin n -> α)
  proof: by
  simp [dotProduct, Fin.sum_univ_succ, vecHead, vecTail]

中文:
定理 dotProduct_cons
  条件: (v : 有限集 n.succ -> α) (x : α) (w : 有限集 n -> α)
  证明: by
  simp [dotProduct, Fin.sum_univ_succ, vecHead, vecTail]

Depends on / 依赖: Fin.sum_univ_succ, dotProduct, sum_univ_succ, vecHead, vecTail
-/
theorem dotProduct_cons (v : Fin n.succ -> α) (x : α) (w : Fin n -> α) :
    v ⬝ᵥ vecCons x w = vecHead v * x + vecTail v ⬝ᵥ w := by
  simp [dotProduct, Fin.sum_univ_succ, vecHead, vecTail]

/--
theorem `cons_dotProduct_cons` / 定理 `cons_dotProduct_cons`

English:
theorem cons_dotProduct_cons
  given: (x : α) (v : Fin n -> α) (y : α) (w : Fin n -> α)
  proof: by simp

中文:
定理 cons_dotProduct_cons
  条件: (x : α) (v : 有限集 n -> α) (y : α) (w : 有限集 n -> α)
  证明: by simp
-/
theorem cons_dotProduct_cons (x : α) (v : Fin n -> α) (y : α) (w : Fin n -> α) :
    vecCons x v ⬝ᵥ vecCons y w = x * y + v ⬝ᵥ w := by simp

end DotProduct

section Diagonal
variable [Zero α]

/--
theorem `diagonal_fin_one` / 定理 `diagonal_fin_one`

English:
theorem diagonal_fin_one
  given: (d : Fin 1 -> α)
  statement: diagonal d = !![d 0]
  proof: by
  simp [← Matrix.ext_iff]

中文:
定理 diagonal_fin_one
  条件: (d : 有限集 1 -> α)
  结论: diagonal d = !![d 0]
  证明: by
  simp [← Matrix.ext_iff]

Depends on / 依赖: Matrix, Matrix.ext_iff, ext_iff
-/
theorem diagonal_fin_one (d : Fin 1 -> α) : diagonal d = !![d 0] := by
  simp [← Matrix.ext_iff]

/--
theorem `diagonal_vec1` / 定理 `diagonal_vec1`

English:
theorem diagonal_vec1
  given: (a : α)
  statement: diagonal ![a] = !![a]
  proof: diagonal_fin_one ![a]

中文:
定理 diagonal_vec1
  条件: (a : α)
  结论: diagonal ![a] = !![a]
  证明: diagonal_fin_one ![a]

Depends on / 依赖: diagonal_fin_one
-/
theorem diagonal_vec1 (a : α) : diagonal ![a] = !![a] :=
  diagonal_fin_one ![a]

/--
theorem `diagonal_fin_two` / 定理 `diagonal_fin_two`

English:
theorem diagonal_fin_two
  given: (d : Fin 2 -> α)
  statement: diagonal d = !![d 0, 0; 0, d 1]
  proof: by
  simp [← Matrix.ext_iff]

中文:
定理 diagonal_fin_two
  条件: (d : 有限集 2 -> α)
  结论: diagonal d = !![d 0, 0; 0, d 1]
  证明: by
  simp [← Matrix.ext_iff]

Depends on / 依赖: Matrix, Matrix.ext_iff, ext_iff
-/
theorem diagonal_fin_two (d : Fin 2 -> α) : diagonal d = !![d 0, 0; 0, d 1] := by
  simp [← Matrix.ext_iff]

/--
theorem `diagonal_vec2` / 定理 `diagonal_vec2`

English:
theorem diagonal_vec2
  given: (a b : α)
  statement: diagonal ![a, b] = !![a, 0; 0, b]
  proof: diagonal_fin_two ![a, b]

中文:
定理 diagonal_vec2
  条件: (a b : α)
  结论: diagonal ![a, b] = !![a, 0; 0, b]
  证明: diagonal_fin_two ![a, b]

Depends on / 依赖: diagonal_fin_two
-/
theorem diagonal_vec2 (a b : α) : diagonal ![a, b] = !![a, 0; 0, b] :=
  diagonal_fin_two ![a, b]

/--
theorem `diagonal_fin_three` / 定理 `diagonal_fin_three`

English:
theorem diagonal_fin_three
  given: (d : Fin 3 -> α)
  proof: by
  simp [← Matrix.ext_iff, Fin.forall_fin_succ]

中文:
定理 diagonal_fin_three
  条件: (d : 有限集 3 -> α)
  证明: by
  simp [← Matrix.ext_iff, Fin.forall_fin_succ]

Depends on / 依赖: Fin.forall_fin_succ, Matrix, Matrix.ext_iff, ext_iff, forall_fin_succ
-/
theorem diagonal_fin_three (d : Fin 3 -> α) :
    diagonal d = !![d 0, 0, 0; 0, d 1, 0; 0, 0, d 2] := by
  simp [← Matrix.ext_iff, Fin.forall_fin_succ]

/--
theorem `diagonal_vec3` / 定理 `diagonal_vec3`

English:
theorem diagonal_vec3
  given: (a b c : α)
  proof: diagonal_fin_three ![a, b, c]

中文:
定理 diagonal_vec3
  条件: (a b c : α)
  证明: diagonal_fin_three ![a, b, c]

Depends on / 依赖: diagonal_fin_three
-/
theorem diagonal_vec3 (a b c : α) :
    diagonal ![a, b, c] = !![a, 0, 0; 0, b, 0; 0, 0, c] :=
  diagonal_fin_three ![a, b, c]

end Diagonal

section ColRow

variable {ι : Type*}

@[simp]
/--
theorem `replicateCol_empty` / 定理 `replicateCol_empty`

English:
theorem replicateCol_empty
  given: (v : Fin 0 -> α)
  statement: replicateCol ι v = of vecEmpty
  proof: empty_eq _

中文:
定理 replicateCol_empty
  条件: (v : 有限集 0 -> α)
  结论: replicateCol ι v = of vecEmpty
  证明: empty_eq _

Depends on / 依赖: empty_eq
-/
theorem replicateCol_empty (v : Fin 0 -> α) : replicateCol ι v = of vecEmpty :=
  empty_eq _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `replicateCol_cons` / 定理 `replicateCol_cons`

English:
theorem replicateCol_cons
  given: (x : α) (u : Fin m -> α)
  proof: by
  ext i j
  refine Fin.cases ?_ ?_ i <;> simp

@[simp]

中文:
定理 replicateCol_cons
  条件: (x : α) (u : 有限集 m -> α)
  证明: by
  ext i j
  refine Fin.cases ?_ ?_ i <;> simp

@[simp]

Depends on / 依赖: Fin.cases
-/
theorem replicateCol_cons (x : α) (u : Fin m -> α) :
    replicateCol ι (vecCons x u) = of (vecCons (fun _ => x) (replicateCol ι u)) := by
  ext i j
  refine Fin.cases ?_ ?_ i <;> simp

@[simp]
/--
theorem `replicateRow_empty` / 定理 `replicateRow_empty`

English:
theorem replicateRow_empty
  statement: replicateRow ι (vecEmpty : Fin 0 -> α) = of fun _ => vecEmpty
  proof: rfl

@[simp]

中文:
定理 replicateRow_empty
  结论: replicateRow ι (vecEmpty : 有限集 0 -> α) = of fun _ => vecEmpty
  证明: rfl

@[simp]
-/
theorem replicateRow_empty : replicateRow ι (vecEmpty : Fin 0 -> α) = of fun _ => vecEmpty := rfl

@[simp]
/--
theorem `replicateRow_cons` / 定理 `replicateRow_cons`

English:
theorem replicateRow_cons
  given: (x : α) (u : Fin m -> α)
  proof: rfl

中文:
定理 replicateRow_cons
  条件: (x : α) (u : 有限集 m -> α)
  证明: rfl
-/
theorem replicateRow_cons (x : α) (u : Fin m -> α) :
    replicateRow ι (vecCons x u) = of fun _ => vecCons x u :=
  rfl

end ColRow

section Transpose

@[simp]
/--
theorem `transpose_empty_rows` / 定理 `transpose_empty_rows`

English:
theorem transpose_empty_rows
  given: (A : Matrix m' (Fin 0) α)
  statement: Aᵀ = of ![]
  proof: empty_eq _

@[simp]

中文:
定理 transpose_empty_rows
  条件: (A : 矩阵 m' (有限集 0) α)
  结论: Aᵀ = of ![]
  证明: empty_eq _

@[simp]

Depends on / 依赖: empty_eq
-/
theorem transpose_empty_rows (A : Matrix m' (Fin 0) α) : Aᵀ = of ![] :=
  empty_eq _

@[simp]
/--
theorem `transpose_empty_cols` / 定理 `transpose_empty_cols`

English:
theorem transpose_empty_cols
  given: (A : Matrix (Fin 0) m' α)
  statement: Aᵀ = of fun _ => ![]
  proof: funext fun _ => empty_eq _

中文:
定理 transpose_empty_cols
  条件: (A : 矩阵 (有限集 0) m' α)
  结论: Aᵀ = of fun _ => ![]
  证明: funext fun _ => empty_eq _

Depends on / 依赖: empty_eq
-/
theorem transpose_empty_cols (A : Matrix (Fin 0) m' α) : Aᵀ = of fun _ => ![] :=
  funext fun _ => empty_eq _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `cons_transpose` / 定理 `cons_transpose`

English:
theorem cons_transpose
  given: (v : n' -> α) (A : Matrix (Fin m) n' α)
  proof: by
  ext i j
  refine Fin.cases ?_ ?_ j <;> simp

@[simp]

中文:
定理 cons_transpose
  条件: (v : n' -> α) (A : 矩阵 (有限集 m) n' α)
  证明: by
  ext i j
  refine Fin.cases ?_ ?_ j <;> simp

@[simp]

Depends on / 依赖: Fin.cases
-/
theorem cons_transpose (v : n' -> α) (A : Matrix (Fin m) n' α) :
    (of (vecCons v A))ᵀ = of fun i => vecCons (v i) (Aᵀ i) := by
  ext i j
  refine Fin.cases ?_ ?_ j <;> simp

@[simp]
/--
theorem `head_transpose` / 定理 `head_transpose`

English:
theorem head_transpose
  given: (A : Matrix m' (Fin n.succ) α)
  proof: rfl

@[simp]

中文:
定理 head_transpose
  条件: (A : 矩阵 m' (有限集 n.succ) α)
  证明: rfl

@[simp]
-/
theorem head_transpose (A : Matrix m' (Fin n.succ) α) :
    vecHead (of.symm Aᵀ) = vecHead ∘ of.symm A :=
  rfl

@[simp]
/--
theorem `tail_transpose` / 定理 `tail_transpose`

English:
theorem tail_transpose
  given: (A : Matrix m' (Fin n.succ) α)
  statement: vecTail (of.symm Aᵀ) = (vecTail ∘ A)ᵀ
  proof: by
  ext i j
  rfl

中文:
定理 tail_transpose
  条件: (A : 矩阵 m' (有限集 n.succ) α)
  结论: vecTail (of.symm Aᵀ) = (vecTail ∘ A)ᵀ
  证明: by
  ext i j
  rfl
-/
theorem tail_transpose (A : Matrix m' (Fin n.succ) α) : vecTail (of.symm Aᵀ) = (vecTail ∘ A)ᵀ := by
  ext i j
  rfl

end Transpose

section Mul

variable [NonUnitalNonAssocSemiring α]

@[simp]
/--
theorem `empty_mul` / 定理 `empty_mul`

English:
theorem empty_mul
  given: [Fintype n'] (A : Matrix (Fin 0) n' α) (B : Matrix n' o' α)
  statement: A * B = of ![]
  proof: empty_eq _

@[simp]

中文:
定理 empty_mul
  条件: [有限类型 n'] (A : 矩阵 (有限集 0) n' α) (B : 矩阵 n' o' α)
  结论: A * B = of ![]
  证明: empty_eq _

@[simp]

Depends on / 依赖: empty_eq
-/
theorem empty_mul [Fintype n'] (A : Matrix (Fin 0) n' α) (B : Matrix n' o' α) : A * B = of ![] :=
  empty_eq _

@[simp]
/--
theorem `empty_mul_empty` / 定理 `empty_mul_empty`

English:
theorem empty_mul_empty
  given: (A : Matrix m' (Fin 0) α) (B : Matrix (Fin 0) o' α)
  statement: A * B = 0
  proof: rfl

@[simp]

中文:
定理 empty_mul_empty
  条件: (A : 矩阵 m' (有限集 0) α) (B : 矩阵 (有限集 0) o' α)
  结论: A * B = 0
  证明: rfl

@[simp]
-/
theorem empty_mul_empty (A : Matrix m' (Fin 0) α) (B : Matrix (Fin 0) o' α) : A * B = 0 :=
  rfl

@[simp]
/--
theorem `mul_empty` / 定理 `mul_empty`

English:
theorem mul_empty
  given: [Fintype n'] (A : Matrix m' n' α) (B : Matrix n' (Fin 0) α)
  proof: funext fun _ => empty_eq _

中文:
定理 mul_empty
  条件: [有限类型 n'] (A : 矩阵 m' n' α) (B : 矩阵 n' (有限集 0) α)
  证明: funext fun _ => empty_eq _

Depends on / 依赖: empty_eq
-/
theorem mul_empty [Fintype n'] (A : Matrix m' n' α) (B : Matrix n' (Fin 0) α) :
    A * B = of fun _ => ![] :=
  funext fun _ => empty_eq _

/--
theorem `mul_val_succ` / 定理 `mul_val_succ`

English:
theorem mul_val_succ
  statement: [Fintype n'] (A : Matrix (Fin m.succ) n' α) (B : Matrix n' o' α) (i : Fin m)
  proof: rfl

@[simp]

中文:
定理 mul_val_succ
  结论: [有限类型 n'] (A : 矩阵 (有限集 m.succ) n' α) (B : 矩阵 n' o' α) (i : 有限集 m)
  证明: rfl

@[simp]
-/
theorem mul_val_succ [Fintype n'] (A : Matrix (Fin m.succ) n' α) (B : Matrix n' o' α) (i : Fin m)
    (j : o') : (A * B) i.succ j = (of (vecTail (of.symm A)) * B) i j :=
  rfl

@[simp]
/--
theorem `cons_mul` / 定理 `cons_mul`

English:
theorem cons_mul
  given: [Fintype n'] (v : n' -> α) (A : Fin m -> n' -> α) (B : Matrix n' o' α)
  proof: by
  ext i j
  refine Fin.cases ?_ ?_ i
  · rfl
  simp [mul_val_succ]

中文:
定理 cons_mul
  条件: [有限类型 n'] (v : n' -> α) (A : 有限集 m -> n' -> α) (B : 矩阵 n' o' α)
  证明: by
  ext i j
  refine Fin.cases ?_ ?_ i
  · rfl
  simp [mul_val_succ]

Depends on / 依赖: Fin.cases, mul_val_succ
-/
theorem cons_mul [Fintype n'] (v : n' -> α) (A : Fin m -> n' -> α) (B : Matrix n' o' α) :
    of (vecCons v A) * B = of (vecCons (v ᵥ* B) (of.symm (of A * B))) := by
  ext i j
  refine Fin.cases ?_ ?_ i
  · rfl
  simp [mul_val_succ]

end Mul

section VecMul

variable [NonUnitalNonAssocSemiring α]

@[simp]
/--
theorem `empty_vecMul` / 定理 `empty_vecMul`

English:
theorem empty_vecMul
  given: (v : Fin 0 -> α) (B : Matrix (Fin 0) o' α)
  statement: v ᵥ* B = 0
  proof: rfl

@[simp]

中文:
定理 empty_vecMul
  条件: (v : 有限集 0 -> α) (B : 矩阵 (有限集 0) o' α)
  结论: v ᵥ* B = 0
  证明: rfl

@[simp]
-/
theorem empty_vecMul (v : Fin 0 -> α) (B : Matrix (Fin 0) o' α) : v ᵥ* B = 0 :=
  rfl

@[simp]
/--
theorem `vecMul_empty` / 定理 `vecMul_empty`

English:
theorem vecMul_empty
  given: [Fintype n'] (v : n' -> α) (B : Matrix n' (Fin 0) α)
  statement: v ᵥ* B = ![]
  proof: empty_eq _

@[simp]

中文:
定理 vecMul_empty
  条件: [有限类型 n'] (v : n' -> α) (B : 矩阵 n' (有限集 0) α)
  结论: v ᵥ* B = ![]
  证明: empty_eq _

@[simp]

Depends on / 依赖: empty_eq
-/
theorem vecMul_empty [Fintype n'] (v : n' -> α) (B : Matrix n' (Fin 0) α) : v ᵥ* B = ![] :=
  empty_eq _

@[simp]
/--
theorem `cons_vecMul` / 定理 `cons_vecMul`

English:
theorem cons_vecMul
  given: (x : α) (v : Fin n -> α) (B : Fin n.succ -> o' -> α)
  proof: by
  ext i
  simp [vecMul]

@[simp]

中文:
定理 cons_vecMul
  条件: (x : α) (v : 有限集 n -> α) (B : 有限集 n.succ -> o' -> α)
  证明: by
  ext i
  simp [vecMul]

@[simp]

Depends on / 依赖: vecMul
-/
theorem cons_vecMul (x : α) (v : Fin n -> α) (B : Fin n.succ -> o' -> α) :
    vecCons x v ᵥ* of B = x • vecHead B + v ᵥ* of (vecTail B) := by
  ext i
  simp [vecMul]

@[simp]
/--
theorem `vecMul_cons` / 定理 `vecMul_cons`

English:
theorem vecMul_cons
  given: (v : Fin n.succ -> α) (w : o' -> α) (B : Fin n -> o' -> α)
  proof: by
  ext i
  simp [vecMul]

中文:
定理 vecMul_cons
  条件: (v : 有限集 n.succ -> α) (w : o' -> α) (B : 有限集 n -> o' -> α)
  证明: by
  ext i
  simp [vecMul]

Depends on / 依赖: vecMul
-/
theorem vecMul_cons (v : Fin n.succ -> α) (w : o' -> α) (B : Fin n -> o' -> α) :
    v ᵥ* of (vecCons w B) = vecHead v • w + vecTail v ᵥ* of B := by
  ext i
  simp [vecMul]

/--
theorem `cons_vecMul_cons` / 定理 `cons_vecMul_cons`

English:
theorem cons_vecMul_cons
  given: (x : α) (v : Fin n -> α) (w : o' -> α) (B : Fin n -> o' -> α)
  proof: by simp

中文:
定理 cons_vecMul_cons
  条件: (x : α) (v : 有限集 n -> α) (w : o' -> α) (B : 有限集 n -> o' -> α)
  证明: by simp
-/
theorem cons_vecMul_cons (x : α) (v : Fin n -> α) (w : o' -> α) (B : Fin n -> o' -> α) :
    vecCons x v ᵥ* of (vecCons w B) = x • w + v ᵥ* of B := by simp

end VecMul

section MulVec

variable [NonUnitalNonAssocSemiring α]

@[simp]
/--
theorem `empty_mulVec` / 定理 `empty_mulVec`

English:
theorem empty_mulVec
  given: [Fintype n'] (A : Matrix (Fin 0) n' α) (v : n' -> α)
  statement: A *ᵥ v = ![]
  proof: empty_eq _

@[simp]

中文:
定理 empty_mulVec
  条件: [有限类型 n'] (A : 矩阵 (有限集 0) n' α) (v : n' -> α)
  结论: A *ᵥ v = ![]
  证明: empty_eq _

@[simp]

Depends on / 依赖: empty_eq
-/
theorem empty_mulVec [Fintype n'] (A : Matrix (Fin 0) n' α) (v : n' -> α) : A *ᵥ v = ![] :=
  empty_eq _

@[simp]
/--
theorem `mulVec_empty` / 定理 `mulVec_empty`

English:
theorem mulVec_empty
  given: (A : Matrix m' (Fin 0) α) (v : Fin 0 -> α)
  statement: A *ᵥ v = 0
  proof: rfl

@[simp]

中文:
定理 mulVec_empty
  条件: (A : 矩阵 m' (有限集 0) α) (v : 有限集 0 -> α)
  结论: A *ᵥ v = 0
  证明: rfl

@[simp]
-/
theorem mulVec_empty (A : Matrix m' (Fin 0) α) (v : Fin 0 -> α) : A *ᵥ v = 0 :=
  rfl

@[simp]
/--
theorem `cons_mulVec` / 定理 `cons_mulVec`

English:
theorem cons_mulVec
  given: [Fintype n'] (v : n' -> α) (A : Fin m -> n' -> α) (w : n' -> α)
  proof: by
  ext i
  refine Fin.cases ?_ ?_ i <;> simp [mulVec]

@[simp]

中文:
定理 cons_mulVec
  条件: [有限类型 n'] (v : n' -> α) (A : 有限集 m -> n' -> α) (w : n' -> α)
  证明: by
  ext i
  refine Fin.cases ?_ ?_ i <;> simp [mulVec]

@[simp]

Depends on / 依赖: Fin.cases, mulVec
-/
theorem cons_mulVec [Fintype n'] (v : n' -> α) (A : Fin m -> n' -> α) (w : n' -> α) :
    (of <| vecCons v A) *ᵥ w = vecCons (v ⬝ᵥ w) (of A *ᵥ w) := by
  ext i
  refine Fin.cases ?_ ?_ i <;> simp [mulVec]

@[simp]
/--
theorem `mulVec_cons` / 定理 `mulVec_cons`

English:
theorem mulVec_cons
  statement: {α} [NonUnitalCommSemiring α] (A : m' -> Fin n.succ -> α) (x : α)
  proof: by
  ext i
  simp [mulVec, mul_comm]

中文:
定理 mulVec_cons
  结论: {α} [非幺交换半环 α] (A : m' -> 有限集 n.succ -> α) (x : α)
  证明: by
  ext i
  simp [mulVec, mul_comm]

Depends on / 依赖: mulVec, mul_comm
-/
theorem mulVec_cons {α} [NonUnitalCommSemiring α] (A : m' -> Fin n.succ -> α) (x : α)
    (v : Fin n -> α) : (of A) *ᵥ (vecCons x v) = x • vecHead ∘ A + (of (vecTail ∘ A)) *ᵥ v := by
  ext i
  simp [mulVec, mul_comm]

end MulVec

section VecMulVec

variable [NonUnitalNonAssocSemiring α]

@[simp]
/--
theorem `empty_vecMulVec` / 定理 `empty_vecMulVec`

English:
theorem empty_vecMulVec
  given: (v : Fin 0 -> α) (w : n' -> α)
  statement: vecMulVec v w = of ![]
  proof: empty_eq _

@[simp]

中文:
定理 empty_vecMulVec
  条件: (v : 有限集 0 -> α) (w : n' -> α)
  结论: vecMulVec v w = of ![]
  证明: empty_eq _

@[simp]

Depends on / 依赖: empty_eq
-/
theorem empty_vecMulVec (v : Fin 0 -> α) (w : n' -> α) : vecMulVec v w = of ![] :=
  empty_eq _

@[simp]
/--
theorem `vecMulVec_empty` / 定理 `vecMulVec_empty`

English:
theorem vecMulVec_empty
  given: (v : m' -> α) (w : Fin 0 -> α)
  statement: vecMulVec v w = of fun _ => ![]
  proof: funext fun _ => empty_eq _

中文:
定理 vecMulVec_empty
  条件: (v : m' -> α) (w : 有限集 0 -> α)
  结论: vecMulVec v w = of fun _ => ![]
  证明: funext fun _ => empty_eq _

Depends on / 依赖: empty_eq
-/
theorem vecMulVec_empty (v : m' -> α) (w : Fin 0 -> α) : vecMulVec v w = of fun _ => ![] :=
  funext fun _ => empty_eq _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `cons_vecMulVec` / 定理 `cons_vecMulVec`

English:
theorem cons_vecMulVec
  given: (x : α) (v : Fin m -> α) (w : n' -> α)
  proof: by
  ext i
  refine Fin.cases ?_ ?_ i <;> simp [vecMulVec]

@[simp]

中文:
定理 cons_vecMulVec
  条件: (x : α) (v : 有限集 m -> α) (w : n' -> α)
  证明: by
  ext i
  refine Fin.cases ?_ ?_ i <;> simp [vecMulVec]

@[simp]

Depends on / 依赖: Fin.cases, vecMulVec
-/
theorem cons_vecMulVec (x : α) (v : Fin m -> α) (w : n' -> α) :
    vecMulVec (vecCons x v) w = vecCons (x • w) (vecMulVec v w) := by
  ext i
  refine Fin.cases ?_ ?_ i <;> simp [vecMulVec]

@[simp]
/--
theorem `vecMulVec_cons` / 定理 `vecMulVec_cons`

English:
theorem vecMulVec_cons
  given: (v : m' -> α) (x : α) (w : Fin n -> α)
  proof: rfl

中文:
定理 vecMulVec_cons
  条件: (v : m' -> α) (x : α) (w : 有限集 n -> α)
  证明: rfl
-/
theorem vecMulVec_cons (v : m' -> α) (x : α) (w : Fin n -> α) :
    vecMulVec v (vecCons x w) = of fun i => v i • vecCons x w := rfl

end VecMulVec

section SMul

variable [NonUnitalNonAssocSemiring α]

/--
theorem `smul_mat_empty` / 定理 `smul_mat_empty`

English:
theorem smul_mat_empty
  given: {m' : Type*} (x : α) (A : Fin 0 -> m' -> α)
  statement: x • A = ![]
  proof: empty_eq _

中文:
定理 smul_mat_empty
  条件: {m' : 类型} (x : α) (A : 有限集 0 -> m' -> α)
  结论: x • A = ![]
  证明: empty_eq _

Depends on / 依赖: empty_eq
-/
theorem smul_mat_empty {m' : Type*} (x : α) (A : Fin 0 -> m' -> α) : x • A = ![] :=
  empty_eq _

end SMul

section Submatrix

@[simp]
/--
theorem `submatrix_empty` / 定理 `submatrix_empty`

English:
theorem submatrix_empty
  given: (A : Matrix m' n' α) (row : Fin 0 -> m') (col : o' -> n')
  proof: empty_eq _

中文:
定理 submatrix_empty
  条件: (A : 矩阵 m' n' α) (row : 有限集 0 -> m') (col : o' -> n')
  证明: empty_eq _

Depends on / 依赖: empty_eq
-/
theorem submatrix_empty (A : Matrix m' n' α) (row : Fin 0 -> m') (col : o' -> n') :
    submatrix A row col = of ![] :=
  empty_eq _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `submatrix_cons_row` / 定理 `submatrix_cons_row`

English:
theorem submatrix_cons_row
  given: (A : Matrix m' n' α) (i : m') (row : Fin m -> m') (col : o' -> n')
  proof: by
  ext i j
  refine Fin.cases ?_ ?_ i <;> simp [submatrix]

中文:
定理 submatrix_cons_row
  条件: (A : 矩阵 m' n' α) (i : m') (row : 有限集 m -> m') (col : o' -> n')
  证明: by
  ext i j
  refine Fin.cases ?_ ?_ i <;> simp [submatrix]

Depends on / 依赖: Fin.cases, submatrix
-/
theorem submatrix_cons_row (A : Matrix m' n' α) (i : m') (row : Fin m -> m') (col : o' -> n') :
    submatrix A (vecCons i row) col = vecCons (fun j => A i (col j)) (submatrix A row col) := by
  ext i j
  refine Fin.cases ?_ ?_ i <;> simp [submatrix]

/-- Updating a row then removing it is the same as removing it. -/
@[simp]
/--
theorem `submatrix_updateRow_succAbove` / 定理 `submatrix_updateRow_succAbove`

English:
theorem submatrix_updateRow_succAbove
  statement: (A : Matrix (Fin m.succ) n' α) (v : n' -> α) (f : o' -> n')
  proof: ext fun r s => (congr_fun (updateRow_ne (Fin.succAbove_ne i r) : _ = A _) (f s) :)

中文:
定理 submatrix_updateRow_succAbove
  结论: (A : 矩阵 (有限集 m.succ) n' α) (v : n' -> α) (f : o' -> n')
  证明: ext fun r s => (congr_fun (updateRow_ne (Fin.succAbove_ne i r) : _ = A _) (f s) :)

Depends on / 依赖: Fin.succAbove_ne, congr_fun, succAbove_ne, updateRow_ne
-/
theorem submatrix_updateRow_succAbove (A : Matrix (Fin m.succ) n' α) (v : n' -> α) (f : o' -> n')
    (i : Fin m.succ) : (A.updateRow i v).submatrix i.succAbove f = A.submatrix i.succAbove f :=
  ext fun r s => (congr_fun (updateRow_ne (Fin.succAbove_ne i r) : _ = A _) (f s) :)

/-- Updating a column then removing it is the same as removing it. -/
@[simp]
/--
theorem `submatrix_updateCol_succAbove` / 定理 `submatrix_updateCol_succAbove`

English:
theorem submatrix_updateCol_succAbove
  statement: (A : Matrix m' (Fin n.succ) α) (v : m' -> α) (f : o' -> m')
  proof: ext fun _r s => updateCol_ne (Fin.succAbove_ne i s)

中文:
定理 submatrix_updateCol_succAbove
  结论: (A : 矩阵 m' (有限集 n.succ) α) (v : m' -> α) (f : o' -> m')
  证明: ext fun _r s => updateCol_ne (Fin.succAbove_ne i s)

Depends on / 依赖: Fin.succAbove_ne, succAbove_ne, updateCol_ne
-/
theorem submatrix_updateCol_succAbove (A : Matrix m' (Fin n.succ) α) (v : m' -> α) (f : o' -> m')
    (i : Fin n.succ) : (A.updateCol i v).submatrix f i.succAbove = A.submatrix f i.succAbove :=
  ext fun _r s => updateCol_ne (Fin.succAbove_ne i s)

end Submatrix

section Vec2AndVec3

section One

variable [Zero α] [One α]

/--
theorem `one_fin_two` / 定理 `one_fin_two`

English:
theorem one_fin_two
  statement: (1 : Matrix (Fin 2) (Fin 2) α) = !![1, 0; 0, 1]
  proof: by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

中文:
定理 one_fin_two
  结论: (1 : 矩阵 (有限集 2) (有限集 2) α) = !![1, 0; 0, 1]
  证明: by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

Depends on / 依赖: fin_cases
-/
theorem one_fin_two : (1 : Matrix (Fin 2) (Fin 2) α) = !![1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/--
theorem `one_fin_three` / 定理 `one_fin_three`

English:
theorem one_fin_three
  statement: (1 : Matrix (Fin 3) (Fin 3) α) = !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  proof: by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

中文:
定理 one_fin_three
  结论: (1 : 矩阵 (有限集 3) (有限集 3) α) = !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  证明: by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

Depends on / 依赖: fin_cases
-/
theorem one_fin_three : (1 : Matrix (Fin 3) (Fin 3) α) = !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end One

section AddMonoidWithOne
variable [AddMonoidWithOne α]

/--
theorem `natCast_fin_two` / 定理 `natCast_fin_two`

English:
theorem natCast_fin_two
  given: (n : Nat)
  statement: (n : Matrix (Fin 2) (Fin 2) α) = !![↑n, 0; 0, ↑n]
  proof: by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

中文:
定理 natCast_fin_two
  条件: (n : 自然数)
  结论: (n : 矩阵 (有限集 2) (有限集 2) α) = !![↑n, 0; 0, ↑n]
  证明: by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

Depends on / 依赖: fin_cases
-/
theorem natCast_fin_two (n : Nat) : (n : Matrix (Fin 2) (Fin 2) α) = !![↑n, 0; 0, ↑n] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/--
theorem `natCast_fin_three` / 定理 `natCast_fin_three`

English:
theorem natCast_fin_three
  given: (n : Nat)
  proof: by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

中文:
定理 natCast_fin_three
  条件: (n : 自然数)
  证明: by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

Depends on / 依赖: fin_cases
-/
theorem natCast_fin_three (n : Nat) :
    (n : Matrix (Fin 3) (Fin 3) α) = !![↑n, 0, 0; 0, ↑n, 0; 0, 0, ↑n] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/--
theorem `ofNat_fin_two` / 定理 `ofNat_fin_two`

English:
theorem ofNat_fin_two
  given: (n : Nat) [n.AtLeastTwo]
  proof: natCast_fin_two _

中文:
定理 of自然数_fin_two
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: natCast_fin_two _

Depends on / 依赖: natCast_fin_two
-/
theorem ofNat_fin_two (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : Matrix (Fin 2) (Fin 2) α) =
      !![ofNat(n), 0; 0, ofNat(n)] :=
  natCast_fin_two _

/--
theorem `ofNat_fin_three` / 定理 `ofNat_fin_three`

English:
theorem ofNat_fin_three
  given: (n : Nat) [n.AtLeastTwo]
  proof: natCast_fin_three _

中文:
定理 of自然数_fin_three
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: natCast_fin_three _

Depends on / 依赖: natCast_fin_three
-/
theorem ofNat_fin_three (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : Matrix (Fin 3) (Fin 3) α) =
      !![ofNat(n), 0, 0; 0, ofNat(n), 0; 0, 0, ofNat(n)] :=
  natCast_fin_three _

end AddMonoidWithOne

/--
theorem `eta_fin_two` / 定理 `eta_fin_two`

English:
theorem eta_fin_two
  given: (A : Matrix (Fin 2) (Fin 2) α)
  statement: A = !![A 0 0, A 0 1; A 1 0, A 1 1]
  proof: by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

中文:
定理 eta_fin_two
  条件: (A : 矩阵 (有限集 2) (有限集 2) α)
  结论: A = !![A 0 0, A 0 1; A 1 0, A 1 1]
  证明: by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

Depends on / 依赖: fin_cases
-/
theorem eta_fin_two (A : Matrix (Fin 2) (Fin 2) α) : A = !![A 0 0, A 0 1; A 1 0, A 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/--
theorem `eta_fin_three` / 定理 `eta_fin_three`

English:
theorem eta_fin_three
  given: (A : Matrix (Fin 3) (Fin 3) α)
  proof: by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

中文:
定理 eta_fin_three
  条件: (A : 矩阵 (有限集 3) (有限集 3) α)
  证明: by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

Depends on / 依赖: fin_cases
-/
theorem eta_fin_three (A : Matrix (Fin 3) (Fin 3) α) :
    A = !![A 0 0, A 0 1, A 0 2;
           A 1 0, A 1 1, A 1 2;
           A 2 0, A 2 1, A 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/--
theorem `mul_fin_two` / 定理 `mul_fin_two`

English:
theorem mul_fin_two
  given: [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α)
  proof: by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

中文:
定理 mul_fin_two
  条件: [加法交换幺半群 α] [乘法 α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α)
  证明: by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

Depends on / 依赖: Fin.sum_univ_succ, Matrix, Matrix.mul_apply, fin_cases, mul_apply, sum_univ_succ
-/
theorem mul_fin_two [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
    !![a₁₁, a₁₂;
       a₂₁, a₂₂] * !![b₁₁, b₁₂;
                      b₂₁, b₂₂] = !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
                                     a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

set_option linter.style.whitespace false in -- Preserve the formatting of the matrices.
/--
theorem `mul_fin_three` / 定理 `mul_fin_three`

English:
theorem mul_fin_three
  statement: [AddCommMonoid α] [Mul α]
  proof: by
  ext i j
  fin_cases i <;> fin_cases j
    <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, ← add_assoc]

中文:
定理 mul_fin_three
  结论: [加法交换幺半群 α] [乘法 α]
  证明: by
  ext i j
  fin_cases i <;> fin_cases j
    <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, ← add_assoc]

Depends on / 依赖: Fin.sum_univ_succ, Matrix, Matrix.mul_apply, add_assoc, fin_cases, mul_apply, sum_univ_succ
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

/--
theorem `vec2_eq` / 定理 `vec2_eq`

English:
theorem vec2_eq
  given: {a₀ a₁ b₀ b₁ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁)
  statement: ![a₀, a₁] = ![b₀, b₁]
  proof: by
  simp [h₀, h₁]

中文:
定理 vec2_eq
  条件: {a₀ a₁ b₀ b₁ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁)
  结论: ![a₀, a₁] = ![b₀, b₁]
  证明: by
  simp [h₀, h₁]
-/
theorem vec2_eq {a₀ a₁ b₀ b₁ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) : ![a₀, a₁] = ![b₀, b₁] := by
  simp [h₀, h₁]

/--
theorem `vec3_eq` / 定理 `vec3_eq`

English:
theorem vec3_eq
  given: {a₀ a₁ a₂ b₀ b₁ b₂ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂)
  proof: by
  simp [h₀, h₁, h₂]

中文:
定理 vec3_eq
  条件: {a₀ a₁ a₂ b₀ b₁ b₂ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂)
  证明: by
  simp [h₀, h₁, h₂]
-/
theorem vec3_eq {a₀ a₁ a₂ b₀ b₁ b₂ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) :
    ![a₀, a₁, a₂] = ![b₀, b₁, b₂] := by
  simp [h₀, h₁, h₂]

/--
theorem `vec2_add` / 定理 `vec2_add`

English:
theorem vec2_add
  given: [Add α] (a₀ a₁ b₀ b₁ : α)
  statement: ![a₀, a₁] + ![b₀, b₁] = ![a₀ + b₀, a₁ + b₁]
  proof: by
  simp

中文:
定理 vec2_add
  条件: [加法 α] (a₀ a₁ b₀ b₁ : α)
  结论: ![a₀, a₁] + ![b₀, b₁] = ![a₀ + b₀, a₁ + b₁]
  证明: by
  simp
-/
theorem vec2_add [Add α] (a₀ a₁ b₀ b₁ : α) : ![a₀, a₁] + ![b₀, b₁] = ![a₀ + b₀, a₁ + b₁] := by
  simp

/--
theorem `vec3_add` / 定理 `vec3_add`

English:
theorem vec3_add
  given: [Add α] (a₀ a₁ a₂ b₀ b₁ b₂ : α)
  proof: by
  simp

中文:
定理 vec3_add
  条件: [加法 α] (a₀ a₁ a₂ b₀ b₁ b₂ : α)
  证明: by
  simp
-/
theorem vec3_add [Add α] (a₀ a₁ a₂ b₀ b₁ b₂ : α) :
    ![a₀, a₁, a₂] + ![b₀, b₁, b₂] = ![a₀ + b₀, a₁ + b₁, a₂ + b₂] := by
  simp

/--
theorem `smul_vec2` / 定理 `smul_vec2`

English:
theorem smul_vec2
  given: {R : Type*} [SMul R α] (x : R) (a₀ a₁ : α)
  proof: by
  simp

中文:
定理 smul_vec2
  条件: {R : 类型} [标量乘法 R α] (x : R) (a₀ a₁ : α)
  证明: by
  simp
-/
theorem smul_vec2 {R : Type*} [SMul R α] (x : R) (a₀ a₁ : α) :
    x • ![a₀, a₁] = ![x • a₀, x • a₁] := by
  simp

/--
theorem `smul_vec3` / 定理 `smul_vec3`

English:
theorem smul_vec3
  given: {R : Type*} [SMul R α] (x : R) (a₀ a₁ a₂ : α)
  proof: by
  simp

中文:
定理 smul_vec3
  条件: {R : 类型} [标量乘法 R α] (x : R) (a₀ a₁ a₂ : α)
  证明: by
  simp
-/
theorem smul_vec3 {R : Type*} [SMul R α] (x : R) (a₀ a₁ a₂ : α) :
    x • ![a₀, a₁, a₂] = ![x • a₀, x • a₁, x • a₂] := by
  simp

variable [AddCommMonoid α] [Mul α]

/--
theorem `vec2_dotProduct'` / 定理 `vec2_dotProduct'`

English:
theorem vec2_dotProduct'
  given: {a₀ a₁ b₀ b₁ : α}
  statement: ![a₀, a₁] ⬝ᵥ ![b₀, b₁] = a₀ * b₀ + a₁ * b₁
  proof: by
  simp

@[simp]

中文:
定理 vec2_dotProduct'
  条件: {a₀ a₁ b₀ b₁ : α}
  结论: ![a₀, a₁] ⬝ᵥ ![b₀, b₁] = a₀ * b₀ + a₁ * b₁
  证明: by
  simp

@[simp]
-/
theorem vec2_dotProduct' {a₀ a₁ b₀ b₁ : α} : ![a₀, a₁] ⬝ᵥ ![b₀, b₁] = a₀ * b₀ + a₁ * b₁ := by
  simp

@[simp]
/--
theorem `vec2_dotProduct` / 定理 `vec2_dotProduct`

English:
theorem vec2_dotProduct
  given: (v w : Fin 2 -> α)
  statement: v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1
  proof: vec2_dotProduct'

中文:
定理 vec2_dotProduct
  条件: (v w : 有限集 2 -> α)
  结论: v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1
  证明: vec2_dotProduct'

Depends on / 依赖: vec2_dotProduct
-/
theorem vec2_dotProduct (v w : Fin 2 -> α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 :=
  vec2_dotProduct'

/--
theorem `vec3_dotProduct'` / 定理 `vec3_dotProduct'`

English:
theorem vec3_dotProduct'
  given: {a₀ a₁ a₂ b₀ b₁ b₂ : α}
  proof: by
  simp [add_assoc]

中文:
定理 vec3_dotProduct'
  条件: {a₀ a₁ a₂ b₀ b₁ b₂ : α}
  证明: by
  simp [add_assoc]

Depends on / 依赖: add_assoc
-/
theorem vec3_dotProduct' {a₀ a₁ a₂ b₀ b₁ b₂ : α} :
    ![a₀, a₁, a₂] ⬝ᵥ ![b₀, b₁, b₂] = a₀ * b₀ + a₁ * b₁ + a₂ * b₂ := by
  simp [add_assoc]

-- This is not tagged `@[simp]` because it does not mesh well with simp lemmas for
-- dot and cross products in dimension 3.
/--
theorem `vec3_dotProduct` / 定理 `vec3_dotProduct`

English:
theorem vec3_dotProduct
  given: (v w : Fin 3 -> α)
  statement: v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2
  proof: vec3_dotProduct'

中文:
定理 vec3_dotProduct
  条件: (v w : 有限集 3 -> α)
  结论: v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2
  证明: vec3_dotProduct'

Depends on / 依赖: vec3_dotProduct
-/
theorem vec3_dotProduct (v w : Fin 3 -> α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 :=
  vec3_dotProduct'

end Vec2AndVec3

end Matrix

@[simp]
/--
lemma `injective_pair_iff_ne` / 引理 `injective_pair_iff_ne`

English:
lemma injective_pair_iff_ne
  given: {α : Type*} {x y : α}
  proof: by
  refine ⟨fun h => ?_, fun h a b h' => ?_⟩
  · simpa using h.ne Fin.zero_ne_one
  · fin_cases a <;> fin_cases b <;> aesop

中文:
引理 injective_pair_iff_ne
  条件: {α : 类型} {x y : α}
  证明: by
  refine ⟨fun h => ?_, fun h a b h' => ?_⟩
  · simpa using h.ne Fin.zero_ne_one
  · fin_cases a <;> fin_cases b <;> aesop

Depends on / 依赖: Fin.zero_ne_one, fin_cases, h.ne, zero_ne_one
-/
lemma injective_pair_iff_ne {α : Type*} {x y : α} :
    Function.Injective ![x, y] ↔ x != y := by
  refine ⟨fun h => ?_, fun h a b h' => ?_⟩
  · simpa using h.ne Fin.zero_ne_one
  · fin_cases a <;> fin_cases b <;> aesop
