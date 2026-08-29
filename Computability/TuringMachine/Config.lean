/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.PartrecBasis
public import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# Modelling partial recursive functions using Turing machines

The files `Config` and `ToPartrec` define a simplified basis for partial recursive functions,
and a `Turing.TM2` model
Turing machine for evaluating these functions. This amounts to a constructive proof that every
`Partrec` function can be evaluated by a Turing machine.

## Main definitions

* `ToPartrec.Code`: a simplified basis for partial recursive functions, valued in
  `List ℕ →. List ℕ`.
  * `ToPartrec.Code.eval`: semantics for a `ToPartrec.Code` program
-/

@[expose] public section

open List (Vector)

open Function (update)

open Relation

namespace Turing

/-!
## A simplified basis for partrec

This section constructs the type `Code`, which is a data type of programs with `List ℕ` input and
output, with enough expressivity to write any partial recursive function. The primitives are:

* `zero'` appends a `0` to the input. That is, `zero' v = 0 :: v`.
* `succ` returns the successor of the head of the input, defaulting to zero if there is no head:
  * `succ [] = [1]`
  * `succ (n :: v) = [n + 1]`
* `tail` returns the tail of the input
  * `tail [] = []`
  * `tail (n :: v) = v`
* `cons f fs` calls `f` and `fs` on the input and conses the results:
  * `cons f fs v = (f v).head :: fs v`
* `comp f g` calls `f` on the output of `g`:
  * `comp f g v = f (g v)`
* `case f g` cases on the head of the input, calling `f` or `g` depending on whether it is zero or
  a successor (similar to `Nat.casesOn`).
  * `case f g [] = f []`
  * `case f g (0 :: v) = f v`
  * `case f g (n+1 :: v) = g (n :: v)`
* `fix f` calls `f` repeatedly, using the head of the result of `f` to decide whether to call `f`
  again or finish:
  * `fix f v = []` if `f v = []`
  * `fix f v = w` if `f v = 0 :: w`
  * `fix f v = fix f w` if `f v = n+1 :: w` (the exact value of `n` is discarded)

This basis is convenient because it is closer to the Turing machine model - the key operations are
splitting and merging of lists of unknown length, while the messy `n`-ary composition operation
from the traditional basis for partial recursive functions is absent - but it retains a
compositional semantics. The first step in transitioning to Turing machines is to make a sequential
evaluator for this basis, which we take up in the next section.
-/


namespace ToPartrec

/--
Inductive type `Code` / 归纳类型 `Code`

English:
inductive Code
  constructors (7):
    - zero': 
    - succ: 
    - tail: 
    - cons: Code -> Code -> Code
    - comp: Code -> Code -> Code
    - case: Code -> Code -> Code
    - fix: Code -> Code

中文:
归纳类型 余de
  构造子 (7 个):
    - zero': 
    - succ: 
    - tail: 
    - cons: 余de -> 余de -> 余de
    - comp: 余de -> 余de -> 余de
    - case: 余de -> 余de -> 余de
    - fix: 余de -> 余de
-/
inductive Code
  | zero'
  | succ
  | tail
  | cons : Code -> Code -> Code
  | comp : Code -> Code -> Code
  | case : Code -> Code -> Code
  | fix : Code -> Code
  deriving DecidableEq, Inhabited

/--
Definition of `Code.eval` / `Code.eval` 的定义

English:
definition Code.eval
  signature: : Code -> List Nat ->. List Nat

中文:
定义 余de.eval
  签名: : 余de -> 列表 自然数 ->. 列表 自然数
-/
def Code.eval : Code -> List Nat ->. List Nat
  | Code.zero' => fun v => pure (0 :: v)
  | Code.succ => fun v => pure [v.headI.succ]
  | Code.tail => fun v => pure v.tail
  | Code.cons f fs => fun v => do
    let n ← Code.eval f v
    let ns ← Code.eval fs v
    pure (n.headI :: ns)
  | Code.comp f g => fun v => g.eval v >>= f.eval
  | Code.case f g => fun v => v.headI.rec (f.eval v.tail) fun y _ => g.eval (y::v.tail)
  | Code.fix f =>
    PFun.fix fun v => (f.eval v).map fun v => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail

namespace Code

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `zero'_eval` / 定理 `zero'_eval`

English:
theorem zero'_eval
  statement: zero'.eval = fun v => pure (0 :: v)
  proof: by simp [eval]

中文:
定理 zero'_eval
  结论: zero'.eval = fun v => pure (0 :: v)
  证明: by simp [eval]
-/
theorem zero'_eval : zero'.eval = fun v => pure (0 :: v) := by simp [eval]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `succ_eval` / 定理 `succ_eval`

English:
theorem succ_eval
  statement: succ.eval = fun v => pure [v.headI.succ]
  proof: by simp [eval]

中文:
定理 succ_eval
  结论: succ.eval = fun v => pure [v.headI.succ]
  证明: by simp [eval]
-/
theorem succ_eval : succ.eval = fun v => pure [v.headI.succ] := by simp [eval]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `tail_eval` / 定理 `tail_eval`

English:
theorem tail_eval
  statement: tail.eval = fun v => pure v.tail
  proof: by simp [eval]

中文:
定理 tail_eval
  结论: tail.eval = fun v => pure v.tail
  证明: by simp [eval]
-/
theorem tail_eval : tail.eval = fun v => pure v.tail := by simp [eval]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `cons_eval` / 定理 `cons_eval`

English:
theorem cons_eval
  given: (f fs)
  statement: (cons f fs).eval = fun v => do {
  proof: by simp [eval]

中文:
定理 cons_eval
  条件: (f fs)
  结论: (cons f fs).eval = fun v => do {
  证明: by simp [eval]
-/
theorem cons_eval (f fs) : (cons f fs).eval = fun v => do {
    let n ← Code.eval f v
    let ns ← Code.eval fs v
    pure (n.headI :: ns) } := by simp [eval]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `comp_eval` / 定理 `comp_eval`

English:
theorem comp_eval
  given: (f g)
  statement: (comp f g).eval = fun v => g.eval v >>= f.eval
  proof: by simp [eval]

中文:
定理 comp_eval
  条件: (f g)
  结论: (comp f g).eval = fun v => g.eval v >>= f.eval
  证明: by simp [eval]
-/
theorem comp_eval (f g) : (comp f g).eval = fun v => g.eval v >>= f.eval := by simp [eval]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `case_eval` / 定理 `case_eval`

English:
theorem case_eval
  given: (f g)
  proof: by
  simp [eval]

@[simp]

中文:
定理 case_eval
  条件: (f g)
  证明: by
  simp [eval]

@[simp]
-/
theorem case_eval (f g) :
    (case f g).eval = fun v => v.headI.rec (f.eval v.tail) fun y _ => g.eval (y::v.tail) := by
  simp [eval]

@[simp]
/--
theorem `fix_eval` / 定理 `fix_eval`

English:
theorem fix_eval
  given: (f)
  statement: (fix f).eval =
  proof: by
  simp [eval]

中文:
定理 fix_eval
  条件: (f)
  结论: (fix f).eval =
  证明: by
  simp [eval]
-/
theorem fix_eval (f) : (fix f).eval =
    PFun.fix fun v => (f.eval v).map fun v =>
      if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail := by
  simp [eval]

/--
Definition of `nil` / `nil` 的定义

English:
definition nil
  signature: : Code
  body: tail.comp succ

@[simp]

中文:
定义 nil
  签名: : 余de
  定义体: tail.comp succ

@[simp]

Depends on / 依赖: tail.comp
-/
def nil : Code :=
  tail.comp succ

@[simp]
/--
theorem `nil_eval` / 定理 `nil_eval`

English:
theorem nil_eval
  given: (v)
  statement: nil.eval v = pure []
  proof: by simp [nil]

中文:
定理 nil_eval
  条件: (v)
  结论: nil.eval v = pure []
  证明: by simp [nil]
-/
theorem nil_eval (v) : nil.eval v = pure [] := by simp [nil]

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : Code
  body: tail.comp zero'

@[simp]

中文:
定义 id
  签名: : 余de
  定义体: tail.comp zero'

@[simp]

Depends on / 依赖: tail.comp
-/
def id : Code :=
  tail.comp zero'

@[simp]
/--
theorem `id_eval` / 定理 `id_eval`

English:
theorem id_eval
  given: (v)
  statement: id.eval v = pure v
  proof: by simp [id]

中文:
定理 id_eval
  条件: (v)
  结论: id.eval v = pure v
  证明: by simp [id]
-/
theorem id_eval (v) : id.eval v = pure v := by simp [id]

/--
Definition of `head` / `head` 的定义

English:
definition head
  signature: : Code
  body: cons id nil

@[simp]

中文:
定义 head
  签名: : 余de
  定义体: cons id nil

@[simp]
-/
def head : Code :=
  cons id nil

@[simp]
/--
theorem `head_eval` / 定理 `head_eval`

English:
theorem head_eval
  given: (v)
  statement: head.eval v = pure [v.headI]
  proof: by simp [head]

中文:
定理 head_eval
  条件: (v)
  结论: head.eval v = pure [v.headI]
  证明: by simp [head]
-/
theorem head_eval (v) : head.eval v = pure [v.headI] := by simp [head]

/--
Definition of `zero` / `zero` 的定义

English:
definition zero
  signature: : Code
  body: cons zero' nil

@[simp]

中文:
定义 zero
  签名: : 余de
  定义体: cons zero' nil

@[simp]
-/
def zero : Code :=
  cons zero' nil

@[simp]
/--
theorem `zero_eval` / 定理 `zero_eval`

English:
theorem zero_eval
  given: (v)
  statement: zero.eval v = pure [0]
  proof: by simp [zero]

中文:
定理 zero_eval
  条件: (v)
  结论: zero.eval v = pure [0]
  证明: by simp [zero]
-/
theorem zero_eval (v) : zero.eval v = pure [0] := by simp [zero]

/--
Definition of `pred` / `pred` 的定义

English:
definition pred
  signature: : Code
  body: case zero head

@[simp]

中文:
定义 pred
  签名: : 余de
  定义体: case zero head

@[simp]
-/
def pred : Code :=
  case zero head

@[simp]
/--
theorem `pred_eval` / 定理 `pred_eval`

English:
theorem pred_eval
  given: (v)
  statement: pred.eval v = pure [v.headI.pred]
  proof: by
  simp [pred]; cases v.headI <;> simp

中文:
定理 pred_eval
  条件: (v)
  结论: pred.eval v = pure [v.headI.pred]
  证明: by
  simp [pred]; cases v.headI <;> simp

Depends on / 依赖: v.headI
-/
theorem pred_eval (v) : pred.eval v = pure [v.headI.pred] := by
  simp [pred]; cases v.headI <;> simp

/--
Definition of `rfind` / `rfind` 的定义

English:
definition rfind
  signature: (f : Code)
  body: comp pred comp (fix <| cons f <| cons succ tail) zero'

中文:
定义 rfind
  签名: (f : 余de)
  定义体: comp pred comp (fix <| cons f <| cons succ tail) zero'
-/
def rfind (f : Code) : Code :=
comp pred comp (fix <| cons f <| cons succ tail) zero'

/--
Definition of `prec` / `prec` 的定义

English:
definition prec
  signature: (f g : Code)
  body: let G :=
cons tail
cons succ
cons (comp pred tail)
cons (comp g <| cons id <| comp tail tail) comp tail comp tail tail
let F := case id comp (comp (comp tail tail) (fix G)) zero'
  cons (comp F (cons head <| cons (comp f tail) tail)) nil

中文:
定义 prec
  签名: (f g : 余de)
  定义体: let G :=
cons tail
cons succ
cons (comp pred tail)
cons (comp g <| cons id <| comp tail tail) comp tail comp tail tail
let F := case id comp (comp (comp tail tail) (fix G)) zero'
  cons (comp F (cons head <| cons (comp f tail) tail)) nil
-/
def prec (f g : Code) : Code :=
  let G :=
cons tail
cons succ
cons (comp pred tail)
cons (comp g <| cons id <| comp tail tail) comp tail comp tail tail
let F := case id comp (comp (comp tail tail) (fix G)) zero'
  cons (comp F (cons head <| cons (comp f tail) tail)) nil

attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_code.comp` / 定理 `exists_code.comp`

English:
theorem exists_code.comp
  statement: {m n} {f : List.Vector Nat n ->. Nat} {g : Fin n -> List.Vector Nat m ->. Nat}
  proof: by
  rsuffices ⟨cg, hg⟩ :
    exists c : Code, forall v : List.Vector Nat m,
c.eval v.1 = Subtype.val < > List.Vector.mOfFn fun i => g i v
  · obtain ⟨cf, hf⟩ := hf
    exact
      ⟨cf.comp cg, fun v => by
        simp [hg, hf, map_bind]
        rfl⟩
  clear hf f
  induction n with
  | zero => exact ⟨nil, fun v => by simp [Vector.mOfFn]; rfl⟩
  | succ n IH =>
    obtain ⟨cg, hg₁⟩ := hg 0
    obtain ⟨cl, hl⟩ := IH fun i => hg i.succ
    exact
      ⟨cons cg cl, fun v => by
        simp [Vector.mOfFn, hg₁, hl]
        rfl⟩

中文:
定理 存在_code.comp
  结论: {m n} {f : 列表.Vector 自然数 n ->. 自然数} {g : 有限集 n -> 列表.Vector 自然数 m ->. 自然数}
  证明: by
  rsuffices ⟨cg, hg⟩ :
    exists c : Code, forall v : List.Vector Nat m,
c.eval v.1 = Subtype.val < > List.Vector.mOfFn fun i => g i v
  · obtain ⟨cf, hf⟩ := hf
    exact
      ⟨cf.comp cg, fun v => by
        simp [hg, hf, map_bind]
        rfl⟩
  clear hf f
  induction n with
  | zero => exact ⟨nil, fun v => by simp [Vector.mOfFn]; rfl⟩
  | succ n IH =>
    obtain ⟨cg, hg₁⟩ := hg 0
    obtain ⟨cl, hl⟩ := IH fun i => hg i.succ
    exact
      ⟨cons cg cl, fun v => by
        simp [Vector.mOfFn, hg₁, hl]
        rfl⟩

Depends on / 依赖: List.Vector, List.Vector.mOfFn, Subtype, Subtype.val, Vector, Vector.mOfFn, c.eval, cf.comp, i.succ, map_bind, rsuffices
-/
theorem exists_code.comp {m n} {f : List.Vector Nat n ->. Nat} {g : Fin n -> List.Vector Nat m ->. Nat}
    (hf : exists c : Code, forall v : List.Vector Nat n, c.eval v.1 = pure <$> f v)
    (hg : forall i, exists c : Code, forall v : List.Vector Nat m, c.eval v.1 = pure <$> g i v) :
    exists c : Code, forall v : List.Vector Nat m,
c.eval v.1 = pure < > ((List.Vector.mOfFn fun i => g i v) >>= f) := by
  rsuffices ⟨cg, hg⟩ :
    exists c : Code, forall v : List.Vector Nat m,
c.eval v.1 = Subtype.val < > List.Vector.mOfFn fun i => g i v
  · obtain ⟨cf, hf⟩ := hf
    exact
      ⟨cf.comp cg, fun v => by
        simp [hg, hf, map_bind]
        rfl⟩
  clear hf f
  induction n with
  | zero => exact ⟨nil, fun v => by simp [Vector.mOfFn]; rfl⟩
  | succ n IH =>
    obtain ⟨cg, hg₁⟩ := hg 0
    obtain ⟨cl, hl⟩ := IH fun i => hg i.succ
    exact
      ⟨cons cg cl, fun v => by
        simp [Vector.mOfFn, hg₁, hl]
        rfl⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_code` / 定理 `exists_code`

English:
theorem exists_code
  given: {n} {f : List.Vector Nat n ->. Nat} (hf : Nat.Partrec' f)
  proof: by
  induction hf with
  | prim hf =>
    induction hf with
    | zero => exact ⟨zero', fun ⟨[], _⟩ => rfl⟩
    | succ => exact ⟨succ, fun ⟨[v], _⟩ => rfl⟩
    | get i =>
      refine Fin.succRec (fun n => ?_) (fun n i IH => ?_) i
      · exact ⟨head, fun ⟨List.cons a as, _⟩ => by simp; rfl⟩
      · obtain ⟨c, h⟩ := IH
        exact ⟨c.comp tail, fun v => by simpa [← Vector.get_tail, Bind.bind] using h v.tail⟩
    | comp g hf hg IHf IHg =>
      simpa [Part.bind_eq_bind] using exists_code.comp IHf IHg
    | @prec n f g _ _ IHf IHg =>
      obtain ⟨cf, hf⟩ := IHf
      obtain ⟨cg, hg⟩ := IHg
      simp only [Part.map_eq_map, Part.map_some, PFun.coe_val] at hf hg
      refine ⟨prec cf cg, fun v => ?_⟩
      rw [← v.cons_head_tail]
      specialize hf v.tail
      replace hg := fun a b => hg (a ::ᵥ b ::ᵥ v.tail)
      simp only [Vector.cons_val, Vector.tail_val] at hf hg
      simp only [Part.map_eq_map, Part.map_some, Vector.cons_val, PFun.coe_val, Vector.tail_val]
      simp only [← Part.pure_eq_some] at hf hg ⊢
      induction v.head with
      | zero => simp [prec, hf, Bind.bind]
      | succ n _ =>
      suffices forall a b, a + b = n ->
        (n.succ :: 0 ::
          g (n ::ᵥ Nat.rec (f v.tail) (fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) n ::ᵥ v.tail) ::
              v.val.tail : List Nat) in
          PFun.fix
            (fun v : List Nat => Part.bind (cg.eval (v.headI :: v.tail.tail))
              (fun x => Part.some (if v.tail.headI = 0
                then Sum.inl
                  (v.headI.succ :: v.tail.headI.pred :: x.headI :: v.tail.tail.tail : List Nat)
                else Sum.inr
                  (v.headI.succ :: v.tail.headI.pred :: x.headI :: v.tail.tail.tail))))
            (a :: b :: Nat.rec (f v.tail) (fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) a :: v.val.tail) by
        have := Part.eq_some_iff.mpr (this _ _ (zero_add _))
        simp [prec, Part.bind_assoc, Bind.bind]
        simp_all
      intro a b e
      induction b generalizing a with
      | zero =>
        refine PFun.mem_fix_iff.2 (Or.inl <| Part.eq_some_iff.1 ?_)
        simp only [hg, ← e, Part.bind_some, List.tail_cons, pure]
        rfl
      | succ b IH =>
        refine PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, IH (a + 1) (by rwa [add_right_comm])⟩)
        simp only [hg, Part.bind_some, List.tail_cons, pure]
        exact Part.mem_some_iff.2 rfl
  | comp g _ _ IHf IHg => exact exists_code.comp IHf IHg
  | @rfind n f _ IHf =>
    obtain ⟨cf, hf⟩ := IHf; refine ⟨rfind cf, fun v => ?_⟩
    replace hf := fun a => hf (a ::ᵥ v)
    simp only [Part.map_eq_map, Part.map_some, Vector.cons_val, PFun.coe_val,
      show forall x, pure x = [x] from fun _ => rfl] at hf ⊢
    refine Part.ext fun x => ?_
    simp only [rfind, Part.bind_eq_bind, Part.pure_eq_some, Part.bind_some,
      cons_eval, comp_eval, fix_eval, tail_eval, succ_eval, zero'_eval,
      List.headI_cons, pred_eval, Part.map_some, false_eq_decide_iff,
      Part.mem_bind_iff, Part.mem_map_iff, Nat.mem_rfind,
      List.tail_cons, true_eq_decide_iff, Part.mem_some_iff, Part.map_bind]
    constructor
    · rintro ⟨v', h1, rfl⟩
      suffices forall v₁ : List Nat, v' in PFun.fix
        (fun v => (cf.eval v).bind fun y => Part.some <|
          if y.headI = 0 then Sum.inl (v.headI.succ :: v.tail)
            else Sum.inr (v.headI.succ :: v.tail)) v₁ ->
        forall n, (v₁ = n :: v.val) -> (forall m < n, ¬f (m ::ᵥ v) = 0) ->
          exists a : Nat,
            (f (a ::ᵥ v) = 0 ∧ forall {m : Nat}, m < a -> ¬f (m ::ᵥ v) = 0) ∧ [a] = [v'.headI.pred]
        this _ h1 0 rfl (by rintro _ ⟨⟩)
      clear h1
      intro v₀ h1
      refine PFun.fixInduction h1 fun v₁ h2 IH => ?_
      clear h1
      rintro n rfl hm
      have := PFun.mem_fix_iff.1 h2
      simp only [hf, Part.bind_some] at this
      split_ifs at this with h
      · simp only [List.headI_cons, exists_false, or_false, Part.mem_some_iff,
          List.tail_cons, false_and, Sum.inl.injEq, reduceCtorEq] at this
        subst this
        exact ⟨_, ⟨h, @hm⟩, rfl⟩
      · refine IH (n.succ::v.val) (by simp_all) _ rfl fun m h' => ?_
        obtain h | rfl := Nat.lt_succ_iff_lt_or_eq.1 h'
        exacts [hm _ h, h]
    · rintro ⟨n, ⟨hn, hm⟩, rfl⟩
      refine ⟨n.succ::v.1, ?_, rfl⟩
      have : (n.succ::v.1 : List Nat) in
        PFun.fix (fun v =>
          (cf.eval v).bind fun y =>
Part.some
              if y.headI = 0 then Sum.inl (v.headI.succ :: v.tail)
                else Sum.inr (v.headI.succ :: v.tail))
            (n::v.val) :=
        PFun.mem_fix_iff.2 (Or.inl (by simp [hf, hn]))
      generalize (n.succ :: v.1 : List Nat) = w at this ⊢
      clear hn
      induction n with
      | zero => exact this
      | succ n IH =>
        refine IH (fun {m} h' => hm (Nat.lt_succ_of_lt h'))
          (PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, this⟩))
        simp only [hf, hm n.lt_succ_self, Part.bind_some, List.headI, if_false,
          Part.mem_some_iff, List.tail_cons]

中文:
定理 存在_code
  条件: {n} {f : 列表.Vector 自然数 n ->. 自然数} (hf : 自然数.Partrec' f)
  证明: by
  induction hf with
  | prim hf =>
    induction hf with
    | zero => exact ⟨zero', fun ⟨[], _⟩ => rfl⟩
    | succ => exact ⟨succ, fun ⟨[v], _⟩ => rfl⟩
    | get i =>
      refine Fin.succRec (fun n => ?_) (fun n i IH => ?_) i
      · exact ⟨head, fun ⟨List.cons a as, _⟩ => by simp; rfl⟩
      · obtain ⟨c, h⟩ := IH
        exact ⟨c.comp tail, fun v => by simpa [← Vector.get_tail, Bind.bind] using h v.tail⟩
    | comp g hf hg IHf IHg =>
      simpa [Part.bind_eq_bind] using exists_code.comp IHf IHg
    | @prec n f g _ _ IHf IHg =>
      obtain ⟨cf, hf⟩ := IHf
      obtain ⟨cg, hg⟩ := IHg
      simp only [Part.map_eq_map, Part.map_some, PFun.coe_val] at hf hg
      refine ⟨prec cf cg, fun v => ?_⟩
      rw [← v.cons_head_tail]
      specialize hf v.tail
      replace hg := fun a b => hg (a ::ᵥ b ::ᵥ v.tail)
      simp only [Vector.cons_val, Vector.tail_val] at hf hg
      simp only [Part.map_eq_map, Part.map_some, Vector.cons_val, PFun.coe_val, Vector.tail_val]
      simp only [← Part.pure_eq_some] at hf hg ⊢
      induction v.head with
      | zero => simp [prec, hf, Bind.bind]
      | succ n _ =>
      suffices forall a b, a + b = n ->
        (n.succ :: 0 ::
          g (n ::ᵥ Nat.rec (f v.tail) (fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) n ::ᵥ v.tail) ::
              v.val.tail : List Nat) in
          PFun.fix
            (fun v : List Nat => Part.bind (cg.eval (v.headI :: v.tail.tail))
              (fun x => Part.some (if v.tail.headI = 0
                then Sum.inl
                  (v.headI.succ :: v.tail.headI.pred :: x.headI :: v.tail.tail.tail : List Nat)
                else Sum.inr
                  (v.headI.succ :: v.tail.headI.pred :: x.headI :: v.tail.tail.tail))))
            (a :: b :: Nat.rec (f v.tail) (fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) a :: v.val.tail) by
        have := Part.eq_some_iff.mpr (this _ _ (zero_add _))
        simp [prec, Part.bind_assoc, Bind.bind]
        simp_all
      intro a b e
      induction b generalizing a with
      | zero =>
        refine PFun.mem_fix_iff.2 (Or.inl <| Part.eq_some_iff.1 ?_)
        simp only [hg, ← e, Part.bind_some, List.tail_cons, pure]
        rfl
      | succ b IH =>
        refine PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, IH (a + 1) (by rwa [add_right_comm])⟩)
        simp only [hg, Part.bind_some, List.tail_cons, pure]
        exact Part.mem_some_iff.2 rfl
  | comp g _ _ IHf IHg => exact exists_code.comp IHf IHg
  | @rfind n f _ IHf =>
    obtain ⟨cf, hf⟩ := IHf; refine ⟨rfind cf, fun v => ?_⟩
    replace hf := fun a => hf (a ::ᵥ v)
    simp only [Part.map_eq_map, Part.map_some, Vector.cons_val, PFun.coe_val,
      show forall x, pure x = [x] from fun _ => rfl] at hf ⊢
    refine Part.ext fun x => ?_
    simp only [rfind, Part.bind_eq_bind, Part.pure_eq_some, Part.bind_some,
      cons_eval, comp_eval, fix_eval, tail_eval, succ_eval, zero'_eval,
      List.headI_cons, pred_eval, Part.map_some, false_eq_decide_iff,
      Part.mem_bind_iff, Part.mem_map_iff, Nat.mem_rfind,
      List.tail_cons, true_eq_decide_iff, Part.mem_some_iff, Part.map_bind]
    constructor
    · rintro ⟨v', h1, rfl⟩
      suffices forall v₁ : List Nat, v' in PFun.fix
        (fun v => (cf.eval v).bind fun y => Part.some <|
          if y.headI = 0 then Sum.inl (v.headI.succ :: v.tail)
            else Sum.inr (v.headI.succ :: v.tail)) v₁ ->
        forall n, (v₁ = n :: v.val) -> (forall m < n, ¬f (m ::ᵥ v) = 0) ->
          exists a : Nat,
            (f (a ::ᵥ v) = 0 ∧ forall {m : Nat}, m < a -> ¬f (m ::ᵥ v) = 0) ∧ [a] = [v'.headI.pred]
        this _ h1 0 rfl (by rintro _ ⟨⟩)
      clear h1
      intro v₀ h1
      refine PFun.fixInduction h1 fun v₁ h2 IH => ?_
      clear h1
      rintro n rfl hm
      have := PFun.mem_fix_iff.1 h2
      simp only [hf, Part.bind_some] at this
      split_ifs at this with h
      · simp only [List.headI_cons, exists_false, or_false, Part.mem_some_iff,
          List.tail_cons, false_and, Sum.inl.injEq, reduceCtorEq] at this
        subst this
        exact ⟨_, ⟨h, @hm⟩, rfl⟩
      · refine IH (n.succ::v.val) (by simp_all) _ rfl fun m h' => ?_
        obtain h | rfl := Nat.lt_succ_iff_lt_or_eq.1 h'
        exacts [hm _ h, h]
    · rintro ⟨n, ⟨hn, hm⟩, rfl⟩
      refine ⟨n.succ::v.1, ?_, rfl⟩
      have : (n.succ::v.1 : List Nat) in
        PFun.fix (fun v =>
          (cf.eval v).bind fun y =>
Part.some
              if y.headI = 0 then Sum.inl (v.headI.succ :: v.tail)
                else Sum.inr (v.headI.succ :: v.tail))
            (n::v.val) :=
        PFun.mem_fix_iff.2 (Or.inl (by simp [hf, hn]))
      generalize (n.succ :: v.1 : List Nat) = w at this ⊢
      clear hn
      induction n with
      | zero => exact this
      | succ n IH =>
        refine IH (fun {m} h' => hm (Nat.lt_succ_of_lt h'))
          (PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, this⟩))
        simp only [hf, hm n.lt_succ_self, Part.bind_some, List.headI, if_false,
          Part.mem_some_iff, List.tail_cons]

Depends on / 依赖: Bind.bind, Fin.succRec, List.cons, Part.bind_eq_bind, Vector, Vector.get_tail, bind_eq_bind, c.comp, exists_code, exists_code.comp, get_tail, succRec, v.tail
-/
theorem exists_code {n} {f : List.Vector Nat n ->. Nat} (hf : Nat.Partrec' f) :
exists c : Code, forall v : List.Vector Nat n, c.eval v.1 = pure < > f v := by
  induction hf with
  | prim hf =>
    induction hf with
    | zero => exact ⟨zero', fun ⟨[], _⟩ => rfl⟩
    | succ => exact ⟨succ, fun ⟨[v], _⟩ => rfl⟩
    | get i =>
      refine Fin.succRec (fun n => ?_) (fun n i IH => ?_) i
      · exact ⟨head, fun ⟨List.cons a as, _⟩ => by simp; rfl⟩
      · obtain ⟨c, h⟩ := IH
        exact ⟨c.comp tail, fun v => by simpa [← Vector.get_tail, Bind.bind] using h v.tail⟩
    | comp g hf hg IHf IHg =>
      simpa [Part.bind_eq_bind] using exists_code.comp IHf IHg
    | @prec n f g _ _ IHf IHg =>
      obtain ⟨cf, hf⟩ := IHf
      obtain ⟨cg, hg⟩ := IHg
      simp only [Part.map_eq_map, Part.map_some, PFun.coe_val] at hf hg
      refine ⟨prec cf cg, fun v => ?_⟩
      rw [← v.cons_head_tail]
      specialize hf v.tail
      replace hg := fun a b => hg (a ::ᵥ b ::ᵥ v.tail)
      simp only [Vector.cons_val, Vector.tail_val] at hf hg
      simp only [Part.map_eq_map, Part.map_some, Vector.cons_val, PFun.coe_val, Vector.tail_val]
      simp only [← Part.pure_eq_some] at hf hg ⊢
      induction v.head with
      | zero => simp [prec, hf, Bind.bind]
      | succ n _ =>
      suffices forall a b, a + b = n ->
        (n.succ :: 0 ::
          g (n ::ᵥ Nat.rec (f v.tail) (fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) n ::ᵥ v.tail) ::
              v.val.tail : List Nat) in
          PFun.fix
            (fun v : List Nat => Part.bind (cg.eval (v.headI :: v.tail.tail))
              (fun x => Part.some (if v.tail.headI = 0
                then Sum.inl
                  (v.headI.succ :: v.tail.headI.pred :: x.headI :: v.tail.tail.tail : List Nat)
                else Sum.inr
                  (v.headI.succ :: v.tail.headI.pred :: x.headI :: v.tail.tail.tail))))
            (a :: b :: Nat.rec (f v.tail) (fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) a :: v.val.tail) by
        have := Part.eq_some_iff.mpr (this _ _ (zero_add _))
        simp [prec, Part.bind_assoc, Bind.bind]
        simp_all
      intro a b e
      induction b generalizing a with
      | zero =>
        refine PFun.mem_fix_iff.2 (Or.inl <| Part.eq_some_iff.1 ?_)
        simp only [hg, ← e, Part.bind_some, List.tail_cons, pure]
        rfl
      | succ b IH =>
        refine PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, IH (a + 1) (by rwa [add_right_comm])⟩)
        simp only [hg, Part.bind_some, List.tail_cons, pure]
        exact Part.mem_some_iff.2 rfl
  | comp g _ _ IHf IHg => exact exists_code.comp IHf IHg
  | @rfind n f _ IHf =>
    obtain ⟨cf, hf⟩ := IHf; refine ⟨rfind cf, fun v => ?_⟩
    replace hf := fun a => hf (a ::ᵥ v)
    simp only [Part.map_eq_map, Part.map_some, Vector.cons_val, PFun.coe_val,
      show forall x, pure x = [x] from fun _ => rfl] at hf ⊢
    refine Part.ext fun x => ?_
    simp only [rfind, Part.bind_eq_bind, Part.pure_eq_some, Part.bind_some,
      cons_eval, comp_eval, fix_eval, tail_eval, succ_eval, zero'_eval,
      List.headI_cons, pred_eval, Part.map_some, false_eq_decide_iff,
      Part.mem_bind_iff, Part.mem_map_iff, Nat.mem_rfind,
      List.tail_cons, true_eq_decide_iff, Part.mem_some_iff, Part.map_bind]
    constructor
    · rintro ⟨v', h1, rfl⟩
      suffices forall v₁ : List Nat, v' in PFun.fix
        (fun v => (cf.eval v).bind fun y => Part.some <|
          if y.headI = 0 then Sum.inl (v.headI.succ :: v.tail)
            else Sum.inr (v.headI.succ :: v.tail)) v₁ ->
        forall n, (v₁ = n :: v.val) -> (forall m < n, ¬f (m ::ᵥ v) = 0) ->
          exists a : Nat,
            (f (a ::ᵥ v) = 0 ∧ forall {m : Nat}, m < a -> ¬f (m ::ᵥ v) = 0) ∧ [a] = [v'.headI.pred]
        this _ h1 0 rfl (by rintro _ ⟨⟩)
      clear h1
      intro v₀ h1
      refine PFun.fixInduction h1 fun v₁ h2 IH => ?_
      clear h1
      rintro n rfl hm
      have := PFun.mem_fix_iff.1 h2
      simp only [hf, Part.bind_some] at this
      split_ifs at this with h
      · simp only [List.headI_cons, exists_false, or_false, Part.mem_some_iff,
          List.tail_cons, false_and, Sum.inl.injEq, reduceCtorEq] at this
        subst this
        exact ⟨_, ⟨h, @hm⟩, rfl⟩
      · refine IH (n.succ::v.val) (by simp_all) _ rfl fun m h' => ?_
        obtain h | rfl := Nat.lt_succ_iff_lt_or_eq.1 h'
        exacts [hm _ h, h]
    · rintro ⟨n, ⟨hn, hm⟩, rfl⟩
      refine ⟨n.succ::v.1, ?_, rfl⟩
      have : (n.succ::v.1 : List Nat) in
        PFun.fix (fun v =>
          (cf.eval v).bind fun y =>
Part.some
              if y.headI = 0 then Sum.inl (v.headI.succ :: v.tail)
                else Sum.inr (v.headI.succ :: v.tail))
            (n::v.val) :=
        PFun.mem_fix_iff.2 (Or.inl (by simp [hf, hn]))
      generalize (n.succ :: v.1 : List Nat) = w at this ⊢
      clear hn
      induction n with
      | zero => exact this
      | succ n IH =>
        refine IH (fun {m} h' => hm (Nat.lt_succ_of_lt h'))
          (PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, this⟩))
        simp only [hf, hm n.lt_succ_self, Part.bind_some, List.headI, if_false,
          Part.mem_some_iff, List.tail_cons]

end Code

/-!
## From compositional semantics to sequential semantics

Our initial sequential model is designed to be as similar as possible to the compositional
semantics in terms of its primitives, but it is a sequential semantics, meaning that rather than
defining an `eval c : List ℕ →. List ℕ` function for each program, defined by recursion on
programs, we have a type `Cfg` with a step function `step : Cfg → Option cfg` that provides a
deterministic evaluation order. In order to do this, we introduce the notion of a *continuation*,
which can be viewed as a `Code` with a hole in it where evaluation is currently taking place.
Continuations can be assigned a `List ℕ →. List ℕ` semantics as well, with the interpretation
being that given a `List ℕ` result returned from the code in the hole, the remainder of the
program will evaluate to a `List ℕ` final value.

The continuations are:

* `halt`: the empty continuation: the hole is the whole program, whatever is returned is the
  final result. In our notation this is just `_`.
* `cons₁ fs v k`: evaluating the first part of a `cons`, that is `k (_ :: fs v)`, where `k` is the
  outer continuation.
* `cons₂ ns k`: evaluating the second part of a `cons`: `k (ns.headI :: _)`. (Technically we don't
  need to hold on to all of `ns` here since we are already committed to taking the head, but this
  is more regular.)
* `comp f k`: evaluating the first part of a composition: `k (f _)`.
* `fix f k`: waiting for the result of `f` in a `fix f` expression:
  `k (if _.headI = 0 then _.tail else fix f (_.tail))`

The type `Cfg` of evaluation states is:

* `ret k v`: we have received a result, and are now evaluating the continuation `k` with result
  `v`; that is, `k v` where `k` is ready to evaluate.
* `halt v`: we are done and the result is `v`.

The main theorem of this section is that for each code `c`, the state `stepNormal c halt v` steps
to `v'` in finitely many steps if and only if `Code.eval c v = some v'`.
-/


/--
Inductive type `Cont` / 归纳类型 `Cont`

English:
inductive Cont
  constructors (5):
    - halt: 
    - cons₁: Code -> List Nat -> Cont -> Cont
    - cons₂: List Nat -> Cont -> Cont
    - comp: Code -> Cont -> Cont
    - fix: Code -> Cont -> Cont

中文:
归纳类型 余nt
  构造子 (5 个):
    - halt: 
    - cons₁: 余de -> 列表 自然数 -> 余nt -> 余nt
    - cons₂: 列表 自然数 -> 余nt -> 余nt
    - comp: 余de -> 余nt -> 余nt
    - fix: 余de -> 余nt -> 余nt
-/
inductive Cont
  | halt
  | cons₁ : Code -> List Nat -> Cont -> Cont
  | cons₂ : List Nat -> Cont -> Cont
  | comp : Code -> Cont -> Cont
  | fix : Code -> Cont -> Cont
  deriving Inhabited

/--
Definition of `Cont.eval` / `Cont.eval` 的定义

English:
definition Cont.eval
  signature: : Cont -> List Nat ->. List Nat

中文:
定义 余nt.eval
  签名: : 余nt -> 列表 自然数 ->. 列表 自然数
-/
def Cont.eval : Cont -> List Nat ->. List Nat
  | Cont.halt => pure
  | Cont.cons₁ fs as k => fun v => do
    let ns ← Code.eval fs as
    Cont.eval k (v.headI :: ns)
  | Cont.cons₂ ns k => fun v => Cont.eval k (ns.headI :: v)
  | Cont.comp f k => fun v => Code.eval f v >>= Cont.eval k
  | Cont.fix f k => fun v => if v.headI = 0 then k.eval v.tail else f.fix.eval v.tail >>= k.eval

/--
Inductive type `Cfg` / 归纳类型 `Cfg`

English:
inductive Cfg
  constructors (2):
    - halt: List Nat -> Cfg
    - ret: Cont -> List Nat -> Cfg

中文:
归纳类型 Cfg
  构造子 (2 个):
    - halt: 列表 自然数 -> Cfg
    - ret: 余nt -> 列表 自然数 -> Cfg
-/
inductive Cfg
  | halt : List Nat -> Cfg
  | ret : Cont -> List Nat -> Cfg
  deriving Inhabited

/--
Definition of `stepNormal` / `stepNormal` 的定义

English:
definition stepNormal
  signature: : Code -> Cont -> List Nat -> Cfg

中文:
定义 stepNormal
  签名: : 余de -> 余nt -> 列表 自然数 -> Cfg
-/
def stepNormal : Code -> Cont -> List Nat -> Cfg
  | Code.zero' => fun k v => Cfg.ret k (0::v)
  | Code.succ => fun k v => Cfg.ret k [v.headI.succ]
  | Code.tail => fun k v => Cfg.ret k v.tail
  | Code.cons f fs => fun k v => stepNormal f (Cont.cons₁ fs v k) v
  | Code.comp f g => fun k v => stepNormal g (Cont.comp f k) v
  | Code.case f g => fun k v =>
    v.headI.rec (stepNormal f k v.tail) fun y _ => stepNormal g k (y::v.tail)
  | Code.fix f => fun k v => stepNormal f (Cont.fix f k) v

/--
Definition of `stepRet` / `stepRet` 的定义

English:
definition stepRet
  signature: : Cont -> List Nat -> Cfg

中文:
定义 stepRet
  签名: : 余nt -> 列表 自然数 -> Cfg
-/
def stepRet : Cont -> List Nat -> Cfg
  | Cont.halt, v => Cfg.halt v
  | Cont.cons₁ fs as k, v => stepNormal fs (Cont.cons₂ v k) as
  | Cont.cons₂ ns k, v => stepRet k (ns.headI :: v)
  | Cont.comp f k, v => stepNormal f k v
  | Cont.fix f k, v => if v.headI = 0 then stepRet k v.tail else stepNormal f (Cont.fix f k) v.tail

/--
Definition of `step` / `step` 的定义

English:
definition step
  signature: : Cfg -> Option Cfg

中文:
定义 step
  签名: : Cfg -> 选项类型 Cfg
-/
def step : Cfg -> Option Cfg
  | Cfg.halt _ => none
  | Cfg.ret k v => some (stepRet k v)

/--
Definition of `Cont.then` / `Cont.then` 的定义

English:
definition Cont.then
  signature: : Cont -> Cont -> Cont

中文:
定义 余nt.then
  签名: : 余nt -> 余nt -> 余nt

Depends on / 依赖: Preorder, WellFoundedLT, to_wellFoundedLT
-/
def Cont.then : Cont -> Cont -> Cont
  | Cont.halt => fun k' => k'
  | Cont.cons₁ fs as k => fun k' => Cont.cons₁ fs as (k.then k')
  | Cont.cons₂ ns k => fun k' => Cont.cons₂ ns (k.then k')
  | Cont.comp f k => fun k' => Cont.comp f (k.then k')
  | Cont.fix f k => fun k' => Cont.fix f (k.then k')

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Cont.then_eval` / 定理 `Cont.then_eval`

English:
theorem Cont.then_eval
  given: {k k' : Cont} {v}
  statement: (k.then k').eval v = k.eval v >>= k'.eval
  proof: by
  induction k generalizing v with
  | halt => simp only [Cont.eval, Cont.then, pure_bind]
  | cons₁ => simp only [Cont.eval, Cont.then, bind_assoc, *]
  | cons₂ => simp only [Cont.eval, Cont.then, *]
  | comp _ _ k_ih => simp only [Cont.eval, Cont.then, bind_assoc, ← k_ih]
  | fix _ _ k_ih =>
    simp only [Cont.eval, Cont.then, *]
    split_ifs <;> [rfl; simp only [← k_ih, bind_assoc]]

中文:
定理 余nt.then_eval
  条件: {k k' : 余nt} {v}
  结论: (k.then k').eval v = k.eval v >>= k'.eval
  证明: by
  induction k generalizing v with
  | halt => simp only [Cont.eval, Cont.then, pure_bind]
  | cons₁ => simp only [Cont.eval, Cont.then, bind_assoc, *]
  | cons₂ => simp only [Cont.eval, Cont.then, *]
  | comp _ _ k_ih => simp only [Cont.eval, Cont.then, bind_assoc, ← k_ih]
  | fix _ _ k_ih =>
    simp only [Cont.eval, Cont.then, *]
    split_ifs <;> [rfl; simp only [← k_ih, bind_assoc]]

Depends on / 依赖: Cont.eval, Cont.then, bind_assoc, generalizing, k_ih, pure_bind, split_ifs
-/
theorem Cont.then_eval {k k' : Cont} {v} : (k.then k').eval v = k.eval v >>= k'.eval := by
  induction k generalizing v with
  | halt => simp only [Cont.eval, Cont.then, pure_bind]
  | cons₁ => simp only [Cont.eval, Cont.then, bind_assoc, *]
  | cons₂ => simp only [Cont.eval, Cont.then, *]
  | comp _ _ k_ih => simp only [Cont.eval, Cont.then, bind_assoc, ← k_ih]
  | fix _ _ k_ih =>
    simp only [Cont.eval, Cont.then, *]
    split_ifs <;> [rfl; simp only [← k_ih, bind_assoc]]

/--
Definition of `Cfg.then` / `Cfg.then` 的定义

English:
definition Cfg.then
  signature: : Cfg -> Cont -> Cfg

中文:
定义 Cfg.then
  签名: : Cfg -> 余nt -> Cfg
-/
def Cfg.then : Cfg -> Cont -> Cfg
  | Cfg.halt v => fun k' => stepRet k' v
  | Cfg.ret k v => fun k' => Cfg.ret (k.then k') v

/--
theorem `stepNormal_then` / 定理 `stepNormal_then`

English:
theorem stepNormal_then
  given: (c) (k k' : Cont) (v)
  proof: by
  induction c generalizing k v with simp only [stepNormal, *]
  | cons c c' ih _ => rw [← ih, Cont.then]
  | comp c c' _ ih' => rw [← ih', Cont.then]
  | case => cases v.headI <;> simp only [Nat.rec_zero]
  | fix c ih => rw [← ih, Cont.then]
  | _ => simp only [Cfg.then]

中文:
定理 stepNormal_then
  条件: (c) (k k' : 余nt) (v)
  证明: by
  induction c generalizing k v with simp only [stepNormal, *]
  | cons c c' ih _ => rw [← ih, Cont.then]
  | comp c c' _ ih' => rw [← ih', Cont.then]
  | case => cases v.headI <;> simp only [Nat.rec_zero]
  | fix c ih => rw [← ih, Cont.then]
  | _ => simp only [Cfg.then]

Depends on / 依赖: Cfg.then, Cont.then, Nat.rec_zero, generalizing, rec_zero, stepNormal, v.headI
-/
theorem stepNormal_then (c) (k k' : Cont) (v) :
    stepNormal c (k.then k') v = (stepNormal c k v).then k' := by
  induction c generalizing k v with simp only [stepNormal, *]
  | cons c c' ih _ => rw [← ih, Cont.then]
  | comp c c' _ ih' => rw [← ih', Cont.then]
  | case => cases v.headI <;> simp only [Nat.rec_zero]
  | fix c ih => rw [← ih, Cont.then]
  | _ => simp only [Cfg.then]

/--
theorem `stepRet_then` / 定理 `stepRet_then`

English:
theorem stepRet_then
  given: {k k' : Cont} {v}
  statement: stepRet (k.then k') v = (stepRet k v).then k'
  proof: by
  induction k generalizing v with simp only [Cont.then, stepRet, *]
  | cons₁ =>
    rw [← stepNormal_then]
    rfl
  | comp =>
    rw [← stepNormal_then]
  | fix _ _ k_ih =>
    split_ifs
    · rw [← k_ih]
    · rw [← stepNormal_then]
      rfl
  | _ => simp only [Cfg.then]

中文:
定理 stepRet_then
  条件: {k k' : 余nt} {v}
  结论: stepRet (k.then k') v = (stepRet k v).then k'
  证明: by
  induction k generalizing v with simp only [Cont.then, stepRet, *]
  | cons₁ =>
    rw [← stepNormal_then]
    rfl
  | comp =>
    rw [← stepNormal_then]
  | fix _ _ k_ih =>
    split_ifs
    · rw [← k_ih]
    · rw [← stepNormal_then]
      rfl
  | _ => simp only [Cfg.then]

Depends on / 依赖: Cfg.then, Cont.then, generalizing, k_ih, split_ifs, stepNormal_then, stepRet
-/
theorem stepRet_then {k k' : Cont} {v} : stepRet (k.then k') v = (stepRet k v).then k' := by
  induction k generalizing v with simp only [Cont.then, stepRet, *]
  | cons₁ =>
    rw [← stepNormal_then]
    rfl
  | comp =>
    rw [← stepNormal_then]
  | fix _ _ k_ih =>
    split_ifs
    · rw [← k_ih]
    · rw [← stepNormal_then]
      rfl
  | _ => simp only [Cfg.then]

open StateTransition

/--
Definition of `Code.Ok` / `Code.Ok` 的定义

English:
definition Code.Ok
  signature: (c : Code)
  body: forall k v, StateTransition.eval step (stepNormal c k v) =
    Code.eval c v >>= fun v => StateTransition.eval step (Cfg.ret k v)

中文:
定义 余de.Ok
  签名: (c : 余de)
  定义体: forall k v, StateTransition.eval step (stepNormal c k v) =
    Code.eval c v >>= fun v => StateTransition.eval step (Cfg.ret k v)

Depends on / 依赖: Cfg.ret, Code.eval, StateTransition, StateTransition.eval, stepNormal
-/
def Code.Ok (c : Code) :=
  forall k v, StateTransition.eval step (stepNormal c k v) =
    Code.eval c v >>= fun v => StateTransition.eval step (Cfg.ret k v)

/--
theorem `Code.Ok.zero` / 定理 `Code.Ok.zero`

English:
theorem Code.Ok.zero
  given: {c} (h : Code.Ok c) {v}
  proof: by
  rw [h]; rw [← bind_pure_comp]; congr; funext v
  exact Part.eq_some_iff.2 (mem_eval.2 ⟨ReflTransGen.single rfl, rfl⟩)

中文:
定理 余de.Ok.zero
  条件: {c} (h : 余de.Ok c) {v}
  证明: by
  rw [h]; rw [← bind_pure_comp]; congr; funext v
  exact Part.eq_some_iff.2 (mem_eval.2 ⟨ReflTransGen.single rfl, rfl⟩)

Depends on / 依赖: Part.eq_some_iff, ReflTransGen, ReflTransGen.single, bind_pure_comp, eq_some_iff, mem_eval, single
-/
theorem Code.Ok.zero {c} (h : Code.Ok c) {v} :
StateTransition.eval step (stepNormal c Cont.halt v) = Cfg.halt < > Code.eval c v := by
  rw [h]; rw [← bind_pure_comp]; congr; funext v
  exact Part.eq_some_iff.2 (mem_eval.2 ⟨ReflTransGen.single rfl, rfl⟩)

/--
theorem `stepNormal.is_ret` / 定理 `stepNormal.is_ret`

English:
theorem stepNormal.is_ret
  given: (c k v)
  statement: exists k' v', stepNormal c k v = Cfg.ret k' v'
  proof: by
  induction c generalizing k v with
  | cons _f fs IHf _IHfs => apply IHf
  | comp f _g _IHf IHg => apply IHg
  | case f g IHf IHg =>
    rw [stepNormal]
    simp only
    cases v.headI <;> [apply IHf; apply IHg]
  | fix f IHf => apply IHf
  | _ => exact ⟨_, _, rfl⟩

中文:
定理 stepNormal.is_ret
  条件: (c k v)
  结论: 存在 k' v', stepNormal c k v = Cfg.ret k' v'
  证明: by
  induction c generalizing k v with
  | cons _f fs IHf _IHfs => apply IHf
  | comp f _g _IHf IHg => apply IHg
  | case f g IHf IHg =>
    rw [stepNormal]
    simp only
    cases v.headI <;> [apply IHf; apply IHg]
  | fix f IHf => apply IHf
  | _ => exact ⟨_, _, rfl⟩

Depends on / 依赖: _IHf, _IHfs, generalizing, stepNormal, v.headI
-/
theorem stepNormal.is_ret (c k v) : exists k' v', stepNormal c k v = Cfg.ret k' v' := by
  induction c generalizing k v with
  | cons _f fs IHf _IHfs => apply IHf
  | comp f _g _IHf IHg => apply IHg
  | case f g IHf IHg =>
    rw [stepNormal]
    simp only
    cases v.headI <;> [apply IHf; apply IHg]
  | fix f IHf => apply IHf
  | _ => exact ⟨_, _, rfl⟩

/--
theorem `cont_eval_fix` / 定理 `cont_eval_fix`

English:
theorem cont_eval_fix
  given: {f k v} (fok : Code.Ok f)
  proof: by
  refine Part.ext fun x => ?_
  simp only [Part.bind_eq_bind, Part.mem_bind_iff]
  constructor
  · suffices forall c, x in eval step c -> forall v c', c = Cfg.then c' (Cont.fix f k) ->
      Reaches step (stepNormal f Cont.halt v) c' ->
        exists v₁ in f.eval v, exists v₂ in if List.headI v₁ = 0 then pure v₁.tail else f.fix.eval v₁.tail,
          x in eval step (Cfg.ret k v₂) by
      intro h
      obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
        this _ h _ _ (stepNormal_then _ Cont.halt _ _) ReflTransGen.refl
      refine ⟨v₂, PFun.mem_fix_iff.2 ?_, h₃⟩
      simp only [Part.eq_some_iff.2 hv₁, Part.map_some]
      split_ifs at hv₂ ⊢
      · rw [Part.mem_some_iff.1 hv₂]
        exact Or.inl (Part.mem_some _)
      · exact Or.inr ⟨_, Part.mem_some _, hv₂⟩
    refine fun c he => evalInduction he fun y h IH => ?_
    rintro v (⟨v'⟩ | ⟨k', v'⟩) rfl hr <;> rw [Cfg.then] at h IH <;> simp only at h IH
    · have := mem_eval.2 ⟨hr, rfl⟩
      rw [fok]; rw [Part.bind_eq_bind]; rw [Part.mem_bind_iff] at this
      obtain ⟨v'', h₁, h₂⟩ := this
      rw [reaches_eval] at h₂
      swap
      · exact ReflTransGen.single rfl
      cases Part.mem_unique h₂ (mem_eval.2 ⟨ReflTransGen.refl, rfl⟩)
      refine ⟨v', h₁, ?_⟩
      rw [stepRet] at h
      revert h
      by_cases he : v'.headI = 0 <;> simp only [if_pos, if_false, he] <;> intro h
      · refine ⟨_, Part.mem_some _, ?_⟩
        rw [reaches_eval]
        · exact h
        exact ReflTransGen.single rfl
      · obtain ⟨k₀, v₀, e₀⟩ := stepNormal.is_ret f Cont.halt v'.tail
        have e₁ := stepNormal_then f Cont.halt (Cont.fix f k) v'.tail
        rw [e₀]; rw [Cont.then]; rw [Cfg.then] at e₁
        simp only at e₁
        obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
          IH (stepRet (k₀.then (Cont.fix f k)) v₀) (by rw [stepRet, if_neg he, e₁]; rfl)
            v'.tail _ stepRet_then (by apply ReflTransGen.single; rw [e₀]; rfl)
        refine ⟨_, PFun.mem_fix_iff.2 ?_, h₃⟩
        simp only [Part.eq_some_iff.2 hv₁, Part.map_some, Part.mem_some_iff]
        split_ifs at hv₂ ⊢ <;> [exact Or.inl (congr_arg Sum.inl (Part.mem_some_iff.1 hv₂));
          exact Or.inr ⟨_, rfl, hv₂⟩]
    · exact IH _ rfl _ _ stepRet_then (ReflTransGen.tail hr rfl)
  · rintro ⟨v', he, hr⟩
    rw [reaches_eval] at hr
    swap
    · exact ReflTransGen.single rfl
    refine PFun.fixInduction he fun v (he : v' in f.fix.eval v) IH => ?_
    rw [fok]; rw [Part.bind_eq_bind]; rw [Part.mem_bind_iff]
    obtain he | ⟨v'', he₁', _⟩ := PFun.mem_fix_iff.1 he
    · obtain ⟨v', he₁, he₂⟩ := (Part.mem_map_iff _).1 he
      split_ifs at he₂ with h; cases he₂
      refine ⟨_, he₁, ?_⟩
      rw [reaches_eval]
      swap
      · exact ReflTransGen.single rfl
      rwa [stepRet, if_pos h]
    · obtain ⟨v₁, he₁, he₂⟩ := (Part.mem_map_iff _).1 he₁'
      split_ifs at he₂ with h; cases he₂
      clear he₁'
      refine ⟨_, he₁, ?_⟩
      rw [reaches_eval]
      swap
      · exact ReflTransGen.single rfl
      rw [stepRet]; rw [if_neg h]
      exact IH v₁.tail ((Part.mem_map_iff _).2 ⟨_, he₁, if_neg h⟩)

中文:
定理 cont_eval_fix
  条件: {f k v} (fok : 余de.Ok f)
  证明: by
  refine Part.ext fun x => ?_
  simp only [Part.bind_eq_bind, Part.mem_bind_iff]
  constructor
  · suffices forall c, x in eval step c -> forall v c', c = Cfg.then c' (Cont.fix f k) ->
      Reaches step (stepNormal f Cont.halt v) c' ->
        exists v₁ in f.eval v, exists v₂ in if List.headI v₁ = 0 then pure v₁.tail else f.fix.eval v₁.tail,
          x in eval step (Cfg.ret k v₂) by
      intro h
      obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
        this _ h _ _ (stepNormal_then _ Cont.halt _ _) ReflTransGen.refl
      refine ⟨v₂, PFun.mem_fix_iff.2 ?_, h₃⟩
      simp only [Part.eq_some_iff.2 hv₁, Part.map_some]
      split_ifs at hv₂ ⊢
      · rw [Part.mem_some_iff.1 hv₂]
        exact Or.inl (Part.mem_some _)
      · exact Or.inr ⟨_, Part.mem_some _, hv₂⟩
    refine fun c he => evalInduction he fun y h IH => ?_
    rintro v (⟨v'⟩ | ⟨k', v'⟩) rfl hr <;> rw [Cfg.then] at h IH <;> simp only at h IH
    · have := mem_eval.2 ⟨hr, rfl⟩
      rw [fok]; rw [Part.bind_eq_bind]; rw [Part.mem_bind_iff] at this
      obtain ⟨v'', h₁, h₂⟩ := this
      rw [reaches_eval] at h₂
      swap
      · exact ReflTransGen.single rfl
      cases Part.mem_unique h₂ (mem_eval.2 ⟨ReflTransGen.refl, rfl⟩)
      refine ⟨v', h₁, ?_⟩
      rw [stepRet] at h
      revert h
      by_cases he : v'.headI = 0 <;> simp only [if_pos, if_false, he] <;> intro h
      · refine ⟨_, Part.mem_some _, ?_⟩
        rw [reaches_eval]
        · exact h
        exact ReflTransGen.single rfl
      · obtain ⟨k₀, v₀, e₀⟩ := stepNormal.is_ret f Cont.halt v'.tail
        have e₁ := stepNormal_then f Cont.halt (Cont.fix f k) v'.tail
        rw [e₀]; rw [Cont.then]; rw [Cfg.then] at e₁
        simp only at e₁
        obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
          IH (stepRet (k₀.then (Cont.fix f k)) v₀) (by rw [stepRet, if_neg he, e₁]; rfl)
            v'.tail _ stepRet_then (by apply ReflTransGen.single; rw [e₀]; rfl)
        refine ⟨_, PFun.mem_fix_iff.2 ?_, h₃⟩
        simp only [Part.eq_some_iff.2 hv₁, Part.map_some, Part.mem_some_iff]
        split_ifs at hv₂ ⊢ <;> [exact Or.inl (congr_arg Sum.inl (Part.mem_some_iff.1 hv₂));
          exact Or.inr ⟨_, rfl, hv₂⟩]
    · exact IH _ rfl _ _ stepRet_then (ReflTransGen.tail hr rfl)
  · rintro ⟨v', he, hr⟩
    rw [reaches_eval] at hr
    swap
    · exact ReflTransGen.single rfl
    refine PFun.fixInduction he fun v (he : v' in f.fix.eval v) IH => ?_
    rw [fok]; rw [Part.bind_eq_bind]; rw [Part.mem_bind_iff]
    obtain he | ⟨v'', he₁', _⟩ := PFun.mem_fix_iff.1 he
    · obtain ⟨v', he₁, he₂⟩ := (Part.mem_map_iff _).1 he
      split_ifs at he₂ with h; cases he₂
      refine ⟨_, he₁, ?_⟩
      rw [reaches_eval]
      swap
      · exact ReflTransGen.single rfl
      rwa [stepRet, if_pos h]
    · obtain ⟨v₁, he₁, he₂⟩ := (Part.mem_map_iff _).1 he₁'
      split_ifs at he₂ with h; cases he₂
      clear he₁'
      refine ⟨_, he₁, ?_⟩
      rw [reaches_eval]
      swap
      · exact ReflTransGen.single rfl
      rw [stepRet]; rw [if_neg h]
      exact IH v₁.tail ((Part.mem_map_iff _).2 ⟨_, he₁, if_neg h⟩)

Depends on / 依赖: Cfg.ret, Cfg.then, Cont.fix, Cont.halt, List.headI, PFun.mem_fix_iff, Part.bind_eq_bind, Part.ext, Part.mem_bind_iff, Reaches, ReflTransGen, ReflTransGen.refl, bind_eq_bind, f.eval, f.fix.eval, mem_bind_iff, mem_fix_iff, stepNormal, stepNormal_then
-/
theorem cont_eval_fix {f k v} (fok : Code.Ok f) :
    eval step (stepNormal f (Cont.fix f k) v) =
      f.fix.eval v >>= fun v => eval step (Cfg.ret k v) := by
  refine Part.ext fun x => ?_
  simp only [Part.bind_eq_bind, Part.mem_bind_iff]
  constructor
  · suffices forall c, x in eval step c -> forall v c', c = Cfg.then c' (Cont.fix f k) ->
      Reaches step (stepNormal f Cont.halt v) c' ->
        exists v₁ in f.eval v, exists v₂ in if List.headI v₁ = 0 then pure v₁.tail else f.fix.eval v₁.tail,
          x in eval step (Cfg.ret k v₂) by
      intro h
      obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
        this _ h _ _ (stepNormal_then _ Cont.halt _ _) ReflTransGen.refl
      refine ⟨v₂, PFun.mem_fix_iff.2 ?_, h₃⟩
      simp only [Part.eq_some_iff.2 hv₁, Part.map_some]
      split_ifs at hv₂ ⊢
      · rw [Part.mem_some_iff.1 hv₂]
        exact Or.inl (Part.mem_some _)
      · exact Or.inr ⟨_, Part.mem_some _, hv₂⟩
    refine fun c he => evalInduction he fun y h IH => ?_
    rintro v (⟨v'⟩ | ⟨k', v'⟩) rfl hr <;> rw [Cfg.then] at h IH <;> simp only at h IH
    · have := mem_eval.2 ⟨hr, rfl⟩
      rw [fok]; rw [Part.bind_eq_bind]; rw [Part.mem_bind_iff] at this
      obtain ⟨v'', h₁, h₂⟩ := this
      rw [reaches_eval] at h₂
      swap
      · exact ReflTransGen.single rfl
      cases Part.mem_unique h₂ (mem_eval.2 ⟨ReflTransGen.refl, rfl⟩)
      refine ⟨v', h₁, ?_⟩
      rw [stepRet] at h
      revert h
      by_cases he : v'.headI = 0 <;> simp only [if_pos, if_false, he] <;> intro h
      · refine ⟨_, Part.mem_some _, ?_⟩
        rw [reaches_eval]
        · exact h
        exact ReflTransGen.single rfl
      · obtain ⟨k₀, v₀, e₀⟩ := stepNormal.is_ret f Cont.halt v'.tail
        have e₁ := stepNormal_then f Cont.halt (Cont.fix f k) v'.tail
        rw [e₀]; rw [Cont.then]; rw [Cfg.then] at e₁
        simp only at e₁
        obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
          IH (stepRet (k₀.then (Cont.fix f k)) v₀) (by rw [stepRet, if_neg he, e₁]; rfl)
            v'.tail _ stepRet_then (by apply ReflTransGen.single; rw [e₀]; rfl)
        refine ⟨_, PFun.mem_fix_iff.2 ?_, h₃⟩
        simp only [Part.eq_some_iff.2 hv₁, Part.map_some, Part.mem_some_iff]
        split_ifs at hv₂ ⊢ <;> [exact Or.inl (congr_arg Sum.inl (Part.mem_some_iff.1 hv₂));
          exact Or.inr ⟨_, rfl, hv₂⟩]
    · exact IH _ rfl _ _ stepRet_then (ReflTransGen.tail hr rfl)
  · rintro ⟨v', he, hr⟩
    rw [reaches_eval] at hr
    swap
    · exact ReflTransGen.single rfl
    refine PFun.fixInduction he fun v (he : v' in f.fix.eval v) IH => ?_
    rw [fok]; rw [Part.bind_eq_bind]; rw [Part.mem_bind_iff]
    obtain he | ⟨v'', he₁', _⟩ := PFun.mem_fix_iff.1 he
    · obtain ⟨v', he₁, he₂⟩ := (Part.mem_map_iff _).1 he
      split_ifs at he₂ with h; cases he₂
      refine ⟨_, he₁, ?_⟩
      rw [reaches_eval]
      swap
      · exact ReflTransGen.single rfl
      rwa [stepRet, if_pos h]
    · obtain ⟨v₁, he₁, he₂⟩ := (Part.mem_map_iff _).1 he₁'
      split_ifs at he₂ with h; cases he₂
      clear he₁'
      refine ⟨_, he₁, ?_⟩
      rw [reaches_eval]
      swap
      · exact ReflTransGen.single rfl
      rw [stepRet]; rw [if_neg h]
      exact IH v₁.tail ((Part.mem_map_iff _).2 ⟨_, he₁, if_neg h⟩)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `code_is_ok` / 定理 `code_is_ok`

English:
theorem code_is_ok
  given: (c)
  statement: Code.Ok c
  proof: by
  induction c with (intro k v; rw [stepNormal])
  | cons f fs IHf IHfs =>
    rw [Code.eval]; rw [IHf]
    simp only [bind_assoc, pure_bind]; congr; funext v
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [stepRet]; rw [IHfs]; congr; funext v'
    refine Eq.trans (b := eval step (stepRet (Cont.cons₂ v k) v')) ?_ (Eq.symm ?_) <;>
      exact reaches_eval (ReflTransGen.single rfl)
  | comp f g IHf IHg =>
    rw [Code.eval]; rw [IHg]
    simp only [bind_assoc]; congr; funext v
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [stepRet]; rw [IHf]
  | case f g IHf IHg =>
    simp only [Code.eval]
    cases v.headI <;> simp only [Nat.rec_zero, Part.bind_eq_bind] <;> [apply IHf; apply IHg]
  | fix f IHf => rw [cont_eval_fix IHf]
  | _ => simp only [Code.eval, pure_bind]

中文:
定理 code_is_ok
  条件: (c)
  结论: 余de.Ok c
  证明: by
  induction c with (intro k v; rw [stepNormal])
  | cons f fs IHf IHfs =>
    rw [Code.eval]; rw [IHf]
    simp only [bind_assoc, pure_bind]; congr; funext v
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [stepRet]; rw [IHfs]; congr; funext v'
    refine Eq.trans (b := eval step (stepRet (Cont.cons₂ v k) v')) ?_ (Eq.symm ?_) <;>
      exact reaches_eval (ReflTransGen.single rfl)
  | comp f g IHf IHg =>
    rw [Code.eval]; rw [IHg]
    simp only [bind_assoc]; congr; funext v
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [stepRet]; rw [IHf]
  | case f g IHf IHg =>
    simp only [Code.eval]
    cases v.headI <;> simp only [Nat.rec_zero, Part.bind_eq_bind] <;> [apply IHf; apply IHg]
  | fix f IHf => rw [cont_eval_fix IHf]
  | _ => simp only [Code.eval, pure_bind]

Depends on / 依赖: Code.eval, Cont.cons, Eq.symm, Eq.trans, ReflTr, ReflTransGen, ReflTransGen.single, bind_assoc, pure_bind, reaches_eval, single, stepNormal, stepRet
-/
theorem code_is_ok (c) : Code.Ok c := by
  induction c with (intro k v; rw [stepNormal])
  | cons f fs IHf IHfs =>
    rw [Code.eval]; rw [IHf]
    simp only [bind_assoc, pure_bind]; congr; funext v
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [stepRet]; rw [IHfs]; congr; funext v'
    refine Eq.trans (b := eval step (stepRet (Cont.cons₂ v k) v')) ?_ (Eq.symm ?_) <;>
      exact reaches_eval (ReflTransGen.single rfl)
  | comp f g IHf IHg =>
    rw [Code.eval]; rw [IHg]
    simp only [bind_assoc]; congr; funext v
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [stepRet]; rw [IHf]
  | case f g IHf IHg =>
    simp only [Code.eval]
    cases v.headI <;> simp only [Nat.rec_zero, Part.bind_eq_bind] <;> [apply IHf; apply IHg]
  | fix f IHf => rw [cont_eval_fix IHf]
  | _ => simp only [Code.eval, pure_bind]

/--
theorem `stepNormal_eval` / 定理 `stepNormal_eval`

English:
theorem stepNormal_eval
  given: (c v)
  statement: eval step (stepNormal c Cont.halt v) = Cfg.halt < > c.eval v
  proof: (code_is_ok c).zero

中文:
定理 stepNormal_eval
  条件: (c v)
  结论: eval step (stepNormal c 余nt.halt v) = Cfg.halt < > c.eval v
  证明: (code_is_ok c).zero

Depends on / 依赖: code_is_ok
-/
theorem stepNormal_eval (c v) : eval step (stepNormal c Cont.halt v) = Cfg.halt < > c.eval v :=
  (code_is_ok c).zero

set_option backward.isDefEq.respectTransparency false in
/--
theorem `stepRet_eval` / 定理 `stepRet_eval`

English:
theorem stepRet_eval
  given: {k v}
  statement: eval step (stepRet k v) = Cfg.halt < > k.eval v
  proof: by
  induction k generalizing v with
  | halt =>
    simp only [Cont.eval, map_pure]
    exact Part.eq_some_iff.2 (mem_eval.2 ⟨ReflTransGen.refl, rfl⟩)
  | cons₁ fs as k IH =>
    rw [Cont.eval]; rw [stepRet]; rw [code_is_ok]
    simp only [← bind_pure_comp, bind_assoc]; congr; funext v'
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [stepRet]; rw [IH]; rw [bind_pure_comp]
  | cons₂ ns k IH => rw [Cont.eval, stepRet]; exact IH
  | comp f k IH =>
    rw [Cont.eval]; rw [stepRet]; rw [code_is_ok]
    simp only [← bind_pure_comp, bind_assoc]; congr; funext v'
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [IH]; rw [bind_pure_comp]
  | fix f k IH =>
    rw [Cont.eval]; rw [stepRet]; simp only
    split_ifs; · exact IH
    simp only [← bind_pure_comp, bind_assoc, cont_eval_fix (code_is_ok _)]
    congr; funext; rw [bind_pure_comp, ← IH]
    exact reaches_eval (ReflTransGen.single rfl)

中文:
定理 stepRet_eval
  条件: {k v}
  结论: eval step (stepRet k v) = Cfg.halt < > k.eval v
  证明: by
  induction k generalizing v with
  | halt =>
    simp only [Cont.eval, map_pure]
    exact Part.eq_some_iff.2 (mem_eval.2 ⟨ReflTransGen.refl, rfl⟩)
  | cons₁ fs as k IH =>
    rw [Cont.eval]; rw [stepRet]; rw [code_is_ok]
    simp only [← bind_pure_comp, bind_assoc]; congr; funext v'
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [stepRet]; rw [IH]; rw [bind_pure_comp]
  | cons₂ ns k IH => rw [Cont.eval, stepRet]; exact IH
  | comp f k IH =>
    rw [Cont.eval]; rw [stepRet]; rw [code_is_ok]
    simp only [← bind_pure_comp, bind_assoc]; congr; funext v'
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [IH]; rw [bind_pure_comp]
  | fix f k IH =>
    rw [Cont.eval]; rw [stepRet]; simp only
    split_ifs; · exact IH
    simp only [← bind_pure_comp, bind_assoc, cont_eval_fix (code_is_ok _)]
    congr; funext; rw [bind_pure_comp, ← IH]
    exact reaches_eval (ReflTransGen.single rfl)

Depends on / 依赖: Cont.eval, Part.eq_some_iff, ReflTransGen, ReflTransGen.refl, ReflTransGen.single, bind_, bind_assoc, bind_pure_comp, code_is_ok, eq_some_iff, generalizing, map_pure, mem_eval, reaches_eval, single, stepRet
-/
theorem stepRet_eval {k v} : eval step (stepRet k v) = Cfg.halt < > k.eval v := by
  induction k generalizing v with
  | halt =>
    simp only [Cont.eval, map_pure]
    exact Part.eq_some_iff.2 (mem_eval.2 ⟨ReflTransGen.refl, rfl⟩)
  | cons₁ fs as k IH =>
    rw [Cont.eval]; rw [stepRet]; rw [code_is_ok]
    simp only [← bind_pure_comp, bind_assoc]; congr; funext v'
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [stepRet]; rw [IH]; rw [bind_pure_comp]
  | cons₂ ns k IH => rw [Cont.eval, stepRet]; exact IH
  | comp f k IH =>
    rw [Cont.eval]; rw [stepRet]; rw [code_is_ok]
    simp only [← bind_pure_comp, bind_assoc]; congr; funext v'
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [IH]; rw [bind_pure_comp]
  | fix f k IH =>
    rw [Cont.eval]; rw [stepRet]; simp only
    split_ifs; · exact IH
    simp only [← bind_pure_comp, bind_assoc, cont_eval_fix (code_is_ok _)]
    congr; funext; rw [bind_pure_comp, ← IH]
    exact reaches_eval (ReflTransGen.single rfl)

end ToPartrec

end Turing
