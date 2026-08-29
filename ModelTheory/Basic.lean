/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
module

public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Basics on First-Order Structures

This file defines first-order languages and structures in the style of the
[Flypitch project](https://flypitch.github.io/), as well as several important maps between
structures.

## Main Definitions

- A `FirstOrder.Language` defines a language as a pair of functions from the natural numbers to
  `Type l`. One sends `n` to the type of `n`-ary functions, and the other sends `n` to the type of
  `n`-ary relations.
- A `FirstOrder.Language.Structure` interprets the symbols of a given `FirstOrder.Language` in the
  context of a given type.
- A `FirstOrder.Language.Hom`, denoted `M →[L] N`, is a map from the `L`-structure `M` to the
  `L`-structure `N` that commutes with the interpretations of functions, and which preserves the
  interpretations of relations (although only in the forward direction).
- A `FirstOrder.Language.Embedding`, denoted `M ↪[L] N`, is an embedding from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.
- A `FirstOrder.Language.Equiv`, denoted `M ≃[L] N`, is an equivalence from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.

## References

For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
  [flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*][flypitch_itp]
-/

@[expose] public section

universe u v u' v' w w'

open Cardinal

namespace FirstOrder

/-! ### Languages and Structures -/


-- intended to be used with explicit universe parameters
set_option linter.checkUnivs false in
/--
Definition of `Language` / `Language` 的定义

English:
structure Language
  parameters: where
  axioms and operations (2):
    - Functions : Nat -> Type u
    - Relations : Nat -> Type v

中文:
结构 Language
  参数: where
  公理与运算 (2 个):
    - Functions : 自然数 -> 类型u
    - Relations : 自然数 -> 类型v
-/
structure Language where
  /-- For every arity, a `Type u` of functions of that arity -/
  Functions : Nat -> Type u
  /-- For every arity, a `Type v` of relations of that arity -/
  Relations : Nat -> Type v

namespace Language

variable (L : Language.{u, v})

/--
Definition of `IsRelational` / `IsRelational` 的定义

English:
abbreviation IsRelational
  signature: : Prop
  body: forall n, IsEmpty (L.Functions n)

中文:
缩写 IsRelational
  签名: : 命题
  定义体: forall n, IsEmpty (L.Functions n)

Depends on / 依赖: Functions, IsEmpty, L.Functions
-/
abbrev IsRelational : Prop := forall n, IsEmpty (L.Functions n)

/--
Definition of `IsAlgebraic` / `IsAlgebraic` 的定义

English:
abbreviation IsAlgebraic
  signature: : Prop
  body: forall n, IsEmpty (L.Relations n)

中文:
缩写 是代数
  签名: : 命题
  定义体: forall n, IsEmpty (L.Relations n)

Depends on / 依赖: IsEmpty, L.Relations, Relations
-/
abbrev IsAlgebraic : Prop := forall n, IsEmpty (L.Relations n)

/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: : Language
  body: ⟨fun _ => Empty, fun _ => Empty⟩
  deriving IsAlgebraic, IsRelational

中文:
定义 empty
  签名: : Language
  定义体: ⟨fun _ => Empty, fun _ => Empty⟩
  deriving IsAlgebraic, IsRelational
-/
protected def empty : Language := ⟨fun _ => Empty, fun _ => Empty⟩
  deriving IsAlgebraic, IsRelational

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Language
  body: ⟨Language.empty⟩

中文:
实例 :
  签名: 可居 Language
  定义体: ⟨Language.empty⟩

Depends on / 依赖: Language, Language.empty
-/
instance : Inhabited Language :=
  ⟨Language.empty⟩

/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: (L' : Language.{u', v'})
  body: ⟨fun n => L.Functions n oplus L'.Functions n, fun n => L.Relations n oplus L'.Relations n⟩

中文:
定义 求和
  签名: (L' : Language.{u', v'})
  定义体: ⟨fun n => L.Functions n oplus L'.Functions n, fun n => L.Relations n oplus L'.Relations n⟩
-/
protected def sum (L' : Language.{u', v'}) : Language :=
  ⟨fun n => L.Functions n oplus L'.Functions n, fun n => L.Relations n oplus L'.Relations n⟩

/--
Definition of `Constants` / `Constants` 的定义

English:
abbreviation Constants
  body: L.Functions 0

中文:
缩写 Constants
  定义体: L.Functions 0
-/
protected abbrev Constants :=
  L.Functions 0

/--
Definition of `Symbols` / `Symbols` 的定义

English:
abbreviation Symbols
  body: (Σ l, L.Functions l) oplus (Σ l, L.Relations l)

中文:
缩写 Symbols
  定义体: (Σ l, L.Functions l) oplus (Σ l, L.Relations l)

Depends on / 依赖: Functions, L.Functions, L.Relations, Relations
-/
abbrev Symbols :=
  (Σ l, L.Functions l) oplus (Σ l, L.Relations l)

/--
Definition of `card` / `card` 的定义

English:
definition card
  signature: : Cardinal
  body: #L.Symbols

中文:
定义 card
  签名: : 基数
  定义体: #L.Symbols

Depends on / 依赖: L.Symbols, Symbols
-/
def card : Cardinal :=
  #L.Symbols

variable {L} {L' : Language.{u', v'}}

/--
theorem `card_eq_card_functions_add_card_relations` / 定理 `card_eq_card_functions_add_card_relations`

English:
theorem card_eq_card_functions_add_card_relations
  proof: by
  simp only [card, mk_sum, mk_sigma, lift_sum]

中文:
定理 card_eq_card_functions_add_card_relations
  证明: by
  simp only [card, mk_sum, mk_sigma, lift_sum]

Depends on / 依赖: lift_sum, mk_sigma, mk_sum
-/
theorem card_eq_card_functions_add_card_relations :
    L.card =
      (Cardinal.sum fun l => Cardinal.lift.{v} #(L.Functions l)) +
        Cardinal.sum fun l => Cardinal.lift.{u} #(L.Relations l) := by
  simp only [card, mk_sum, mk_sigma, lift_sum]

/--
Instance `isRelational_sum` / 实例 `isRelational_sum`

English:
instance isRelational_sum
  signature: [L.IsRelational] [L'.IsRelational]
  body: fun _ => instIsEmptySum

中文:
实例 isRelational_sum
  签名: [L.IsRelational] [L'.IsRelational]
  定义体: fun _ => instIsEmptySum

Depends on / 依赖: instIsEmptySum
-/
instance isRelational_sum [L.IsRelational] [L'.IsRelational] : IsRelational (L.sum L') :=
  fun _ => instIsEmptySum

/--
Instance `isAlgebraic_sum` / 实例 `isAlgebraic_sum`

English:
instance isAlgebraic_sum
  signature: [L.IsAlgebraic] [L'.IsAlgebraic]
  body: fun _ => instIsEmptySum

@[simp]

中文:
实例 isAlgebraic_sum
  签名: [L.是代数] [L'.是代数]
  定义体: fun _ => instIsEmptySum

@[simp]

Depends on / 依赖: instIsEmptySum
-/
instance isAlgebraic_sum [L.IsAlgebraic] [L'.IsAlgebraic] : IsAlgebraic (L.sum L') :=
  fun _ => instIsEmptySum

@[simp]
/--
theorem `card_empty` / 定理 `card_empty`

English:
theorem card_empty
  statement: Language.empty.card = 0
  proof: by simp only [card, mk_sum, mk_sigma, mk_eq_zero,
  sum_const, mk_eq_aleph0, lift_id', mul_zero, add_zero]

中文:
定理 card_empty
  结论: Language.empty.card = 0
  证明: by simp only [card, mk_sum, mk_sigma, mk_eq_zero,
  sum_const, mk_eq_aleph0, lift_id', mul_zero, add_zero]

Depends on / 依赖: add_zero, lift_id, mk_eq_aleph0, mk_eq_zero, mk_sigma, mk_sum, mul_zero, sum_const
-/
theorem card_empty : Language.empty.card = 0 := by simp only [card, mk_sum, mk_sigma, mk_eq_zero,
  sum_const, mk_eq_aleph0, lift_id', mul_zero, add_zero]

/--
Instance `isEmpty_empty` / 实例 `isEmpty_empty`

English:
instance isEmpty_empty
  signature: : IsEmpty Language.empty.Symbols
  body: by
  simp only [Language.Symbols, isEmpty_sum, isEmpty_sigma]
  exact ⟨fun _ => inferInstance, fun _ => inferInstance⟩

中文:
实例 isEmpty_empty
  签名: : 是空 Language.empty.Symbols
  定义体: by
  simp only [Language.Symbols, isEmpty_sum, isEmpty_sigma]
  exact ⟨fun _ => inferInstance, fun _ => inferInstance⟩

Depends on / 依赖: Language, Language.Symbols, Symbols, isEmpty_sigma, isEmpty_sum
-/
instance isEmpty_empty : IsEmpty Language.empty.Symbols := by
  simp only [Language.Symbols, isEmpty_sum, isEmpty_sigma]
  exact ⟨fun _ => inferInstance, fun _ => inferInstance⟩

/--
Instance `Countable.countable_functions` / 实例 `Countable.countable_functions`

English:
instance Countable.countable_functions
  signature: [h : Countable L.Symbols]
  body: @Function.Injective.countable _ _ h _ Sum.inl_injective

@[simp]

中文:
实例 可数.countable_functions
  签名: [h : 可数 L.Symbols]
  定义体: @Function.Injective.countable _ _ h _ Sum.inl_injective

@[simp]

Depends on / 依赖: Function, Function.Injective.countable, Injective, Sum.inl_injective, countable, inl_injective
-/
instance Countable.countable_functions [h : Countable L.Symbols] : Countable (Σ l, L.Functions l) :=
  @Function.Injective.countable _ _ h _ Sum.inl_injective

@[simp]
/--
theorem `card_functions_sum` / 定理 `card_functions_sum`

English:
theorem card_functions_sum
  given: (i : Nat)
  proof: by
  simp [Language.sum]

@[simp]

中文:
定理 card_functions_sum
  条件: (i : 自然数)
  证明: by
  simp [Language.sum]

@[simp]

Depends on / 依赖: Language, Language.sum
-/
theorem card_functions_sum (i : Nat) :
    #((L.sum L').Functions i)
      = (Cardinal.lift.{u'} #(L.Functions i) + Cardinal.lift.{u} #(L'.Functions i) : Cardinal) := by
  simp [Language.sum]

@[simp]
/--
theorem `card_relations_sum` / 定理 `card_relations_sum`

English:
theorem card_relations_sum
  given: (i : Nat)
  proof: by
  simp [Language.sum]

中文:
定理 card_relations_sum
  条件: (i : 自然数)
  证明: by
  simp [Language.sum]

Depends on / 依赖: Language, Language.sum
-/
theorem card_relations_sum (i : Nat) :
    #((L.sum L').Relations i) =
      Cardinal.lift.{v'} #(L.Relations i) + Cardinal.lift.{v} #(L'.Relations i) := by
  simp [Language.sum]

/--
theorem `card_sum` / 定理 `card_sum`

English:
theorem card_sum
  proof: by
  simp only [card, mk_sum, mk_sigma, card_functions_sum, sum_add_distrib', lift_add, lift_sum,
    lift_lift, card_relations_sum, add_assoc,
    add_comm (Cardinal.sum fun i => (#(L'.Functions i)).lift)]

中文:
定理 card_sum
  证明: by
  simp only [card, mk_sum, mk_sigma, card_functions_sum, sum_add_distrib', lift_add, lift_sum,
    lift_lift, card_relations_sum, add_assoc,
    add_comm (Cardinal.sum fun i => (#(L'.Functions i)).lift)]

Depends on / 依赖: Cardinal, Cardinal.sum, Functions, add_assoc, add_comm, card_functions_sum, card_relations_sum, lift_add, lift_lift, lift_sum, mk_sigma, mk_sum, sum_add_distrib
-/
theorem card_sum :
    (L.sum L').card = Cardinal.lift.{max u' v'} L.card + Cardinal.lift.{max u v} L'.card := by
  simp only [card, mk_sum, mk_sigma, card_functions_sum, sum_add_distrib', lift_add, lift_sum,
    lift_lift, card_relations_sum, add_assoc,
    add_comm (Cardinal.sum fun i => (#(L'.Functions i)).lift)]

/--
Instance `instDecidableEqFunctions` / 实例 `instDecidableEqFunctions`

English:
instance instDecidableEqFunctions
  signature: {f : Nat -> Type*} {R : Nat -> Type*} (n : Nat) [DecidableEq (f n)]
  body: inferInstance

中文:
实例 instDecidableEqFunctions
  签名: {f : 自然数 -> 类型} {R : 自然数 -> 类型} (n : 自然数) [DecidableEq (f n)]
  定义体: inferInstance
-/
instance instDecidableEqFunctions {f : Nat -> Type*} {R : Nat -> Type*} (n : Nat) [DecidableEq (f n)] :
    DecidableEq ((⟨f, R⟩ : Language).Functions n) := inferInstance

/--
Instance `instDecidableEqRelations` / 实例 `instDecidableEqRelations`

English:
instance instDecidableEqRelations
  signature: {f : Nat -> Type*} {R : Nat -> Type*} (n : Nat) [DecidableEq (R n)]
  body: inferInstance

中文:
实例 instDecidableEqRelations
  签名: {f : 自然数 -> 类型} {R : 自然数 -> 类型} (n : 自然数) [DecidableEq (R n)]
  定义体: inferInstance
-/
instance instDecidableEqRelations {f : Nat -> Type*} {R : Nat -> Type*} (n : Nat) [DecidableEq (R n)] :
    DecidableEq ((⟨f, R⟩ : Language).Relations n) := inferInstance

variable (L) (M : Type w)

/-- A first-order structure on a type `M` consists of interpretations of all the symbols in a given
  language. Each function of arity `n` is interpreted as a function sending tuples of length `n`
  (modeled as `(Fin n → M)`) to `M`, and a relation of arity `n` is a function from tuples of length
  `n` to `Prop`. -/
@[ext]
/--
Definition of `Structure` / `Structure` 的定义

English:
class Structure
  parameters: where
  axioms and operations (2):
    - funMap : forall {n}, L.Functions n -> (Fin n -> M) -> M  [default: by exact fun {n} => isEmptyElim]
    - RelMap : forall {n}, L.Relations n -> (Fin n -> M) -> Prop  [default: by exact fun {n} => isEmptyElim]

中文:
类 结构
  参数: where
  公理与运算 (2 个):
    - funMap : 对任意 {n}, L.函数 n -> (有限集 n -> M) -> M  [默认: by exact fun {n} => isEmptyElim]
    - RelMap : 对任意 {n}, L.关系 n -> (有限集 n -> M) -> 命题  [默认: by exact fun {n} => isEmptyElim]

Depends on / 依赖: isEmptyElim
-/
class Structure where
  /-- Interpretation of the function symbols -/
  funMap : forall {n}, L.Functions n -> (Fin n -> M) -> M := by
    exact fun {n} => isEmptyElim
  /-- Interpretation of the relation symbols -/
  RelMap : forall {n}, L.Relations n -> (Fin n -> M) -> Prop := by
    exact fun {n} => isEmptyElim

variable (N : Type w') [L.Structure M] [L.Structure N]

open Structure

/-- Used for defining `FirstOrder.Language.Theory.ModelType.instInhabited`. -/
@[instance_reducible]
/--
Definition of `Inhabited.trivialStructure` / `Inhabited.trivialStructure` 的定义

English:
definition Inhabited.trivialStructure
  signature: {α : Type*} [Inhabited α]
  body: ⟨default, default⟩

中文:
定义 可居.trivialStructure
  签名: {α : 类型} [可居 α]
  定义体: ⟨default, default⟩
-/
def Inhabited.trivialStructure {α : Type*} [Inhabited α] : L.Structure α :=
  ⟨default, default⟩

/-! ### Maps -/


/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: where
  axioms and operations (3):
    - toFun : M -> N
    - map_fun' : forall {n} (f : L.Functions n) (x), toFun (funMap f x) = funMap f (toFun ∘ x)  [default: by intros; trivial]
    - map_rel' : forall {n} (r : L.Relations n) (x), RelMap r x -> RelMap r (toFun ∘ x)  [default: by intros; trivial]

中文:
结构 态射
  参数: where
  公理与运算 (3 个):
    - toFun : M -> N
    - map_fun' : 对任意 {n} (f : L.函数 n) (x), toFun (funMap f x) = funMap f (toFun ∘ x)  [默认: by intros; trivial]
    - map_rel' : 对任意 {n} (r : L.关系 n) (x), RelMap r x -> RelMap r (toFun ∘ x)  [默认: by intros; trivial]

Depends on / 依赖: intros
-/
structure Hom where
  /-- The underlying function of a homomorphism of structures -/
  toFun : M -> N
  /-- The homomorphism commutes with the interpretations of the function symbols -/
  -- Porting note:
  -- The autoparam here used to be `obviously`. We would like to replace it with `aesop`
  -- but that isn't currently sufficient.
  -- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Aesop.20and.20cases
  -- If that can be improved, we should change this to `by aesop` and remove the proofs below.
  map_fun' : forall {n} (f : L.Functions n) (x), toFun (funMap f x) = funMap f (toFun ∘ x) := by
    intros; trivial
  /-- The homomorphism sends related elements to related elements -/
  map_rel' : forall {n} (r : L.Relations n) (x), RelMap r x -> RelMap r (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial

@[inherit_doc]
scoped[FirstOrder] notation:25 A " ->[" L "] " B => FirstOrder.Language.Hom L A B

/--
Definition of `Embedding` / `Embedding` 的定义

English:
structure Embedding
  parameters: extends M ↪ N
  extends: M ↪ N
  axioms and operations (2):
    - map_fun' : forall {n} (f : L.Functions n) (x), toFun (funMap f x) = funMap f (toFun ∘ x)  [default: by intros; trivial]
    - map_rel' : forall {n} (r : L.Relations n) (x), RelMap r (toFun ∘ x) ↔ RelMap r x  [default: by intros; trivial]

中文:
结构 嵌入
  参数: extends M ↪ N
  继承: M ↪ N
  公理与运算 (2 个):
    - map_fun' : 对任意 {n} (f : L.函数 n) (x), toFun (funMap f x) = funMap f (toFun ∘ x)  [默认: by intros; trivial]
    - map_rel' : 对任意 {n} (r : L.关系 n) (x), RelMap r (toFun ∘ x) ↔ RelMap r x  [默认: by intros; trivial]
-/
structure Embedding extends M ↪ N where
  map_fun' : forall {n} (f : L.Functions n) (x), toFun (funMap f x) = funMap f (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial
  map_rel' : forall {n} (r : L.Relations n) (x), RelMap r (toFun ∘ x) ↔ RelMap r x := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial

@[inherit_doc]
scoped[FirstOrder] notation:25 A " ↪[" L "] " B => FirstOrder.Language.Embedding L A B

/--
Definition of `Equiv` / `Equiv` 的定义

English:
structure Equiv
  parameters: extends M ≃ N
  extends: M ≃ N
  axioms and operations (2):
    - map_fun' : forall {n} (f : L.Functions n) (x), toFun (funMap f x) = funMap f (toFun ∘ x)  [default: by intros; trivial]
    - map_rel' : forall {n} (r : L.Relations n) (x), RelMap r (toFun ∘ x) ↔ RelMap r x  [default: by intros; trivial]

中文:
结构 等价
  参数: extends M ≃ N
  继承: M ≃ N
  公理与运算 (2 个):
    - map_fun' : 对任意 {n} (f : L.函数 n) (x), toFun (funMap f x) = funMap f (toFun ∘ x)  [默认: by intros; trivial]
    - map_rel' : 对任意 {n} (r : L.关系 n) (x), RelMap r (toFun ∘ x) ↔ RelMap r x  [默认: by intros; trivial]
-/
structure Equiv extends M ≃ N where
  map_fun' : forall {n} (f : L.Functions n) (x), toFun (funMap f x) = funMap f (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial
  map_rel' : forall {n} (r : L.Relations n) (x), RelMap r (toFun ∘ x) ↔ RelMap r x := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial

@[inherit_doc]
scoped[FirstOrder] notation:25 A " ≃[" L "] " B => FirstOrder.Language.Equiv L A B

variable {L M N} {P : Type*} [L.Structure P] {Q : Type*} [L.Structure Q]

/-- Interpretation of a constant symbol -/
@[coe]
/--
Definition of `constantMap` / `constantMap` 的定义

English:
definition constantMap
  signature: (c : L.Constants)
  body: funMap c default

中文:
定义 constantMap
  签名: (c : L.Constants)
  定义体: funMap c default

Depends on / 依赖: funMap
-/
def constantMap (c : L.Constants) : M := funMap c default

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC L.Constants M
  body: ⟨constantMap⟩

中文:
实例 :
  签名: CoeTC L.Constants M
  定义体: ⟨constantMap⟩

Depends on / 依赖: constantMap
-/
instance : CoeTC L.Constants M :=
  ⟨constantMap⟩

/--
theorem `funMap_eq_coe_constants` / 定理 `funMap_eq_coe_constants`

English:
theorem funMap_eq_coe_constants
  given: {c : L.Constants} {x : Fin 0 -> M}
  statement: funMap c x = c
  proof: congr rfl (funext finZeroElim)

中文:
定理 funMap_eq_coe_constants
  条件: {c : L.Constants} {x : 有限集 0 -> M}
  结论: funMap c x = c
  证明: congr rfl (funext finZeroElim)

Depends on / 依赖: finZeroElim
-/
theorem funMap_eq_coe_constants {c : L.Constants} {x : Fin 0 -> M} : funMap c x = c :=
  congr rfl (funext finZeroElim)

variable (L M) in
/--
theorem `nonempty_of_nonempty_constants` / 定理 `nonempty_of_nonempty_constants`

English:
theorem nonempty_of_nonempty_constants
  given: [h : Nonempty L.Constants]
  statement: Nonempty M
  proof: h.map (↑)

中文:
定理 nonempty_of_nonempty_constants
  条件: [h : 非空 L.Constants]
  结论: 非空 M
  证明: h.map (↑)

Depends on / 依赖: h.map
-/
theorem nonempty_of_nonempty_constants [h : Nonempty L.Constants] : Nonempty M :=
  h.map (↑)

/--
Definition of `HomClass` / `HomClass` 的定义

English:
class HomClass
  parameters: (L : outParam Language) (F : Type*) (M N : outParam Type*)
  axioms and operations (2):
    - map_fun : forall (φ : F) {n} (f : L.Functions n) (x), φ (funMap f x) = funMap f (φ ∘ x)
    - map_rel : forall (φ : F) {n} (r : L.Relations n) (x), RelMap r x -> RelMap r (φ ∘ x)

中文:
类 态射类
  参数: (L : outParam Language) (F : 类型) (M N : outParam 类型)
  公理与运算 (2 个):
    - map_fun : 对任意 (φ : F) {n} (f : L.函数 n) (x), φ (funMap f x) = funMap f (φ ∘ x)
    - map_rel : 对任意 (φ : F) {n} (r : L.关系 n) (x), RelMap r x -> RelMap r (φ ∘ x)
-/
class HomClass (L : outParam Language) (F : Type*) (M N : outParam Type*)
  [FunLike F M N] [L.Structure M] [L.Structure N] : Prop where
  map_fun : forall (φ : F) {n} (f : L.Functions n) (x), φ (funMap f x) = funMap f (φ ∘ x)
  map_rel : forall (φ : F) {n} (r : L.Relations n) (x), RelMap r x -> RelMap r (φ ∘ x)

/--
Definition of `StrongHomClass` / `StrongHomClass` 的定义

English:
class StrongHomClass
  parameters: (L : outParam Language) (F : Type*) (M N : outParam Type*)
  axioms and operations (2):
    - map_fun : forall (φ : F) {n} (f : L.Functions n) (x), φ (funMap f x) = funMap f (φ ∘ x)
    - map_rel : forall (φ : F) {n} (r : L.Relations n) (x), RelMap r (φ ∘ x) ↔ RelMap r x

中文:
类 Strong态射类
  参数: (L : outParam Language) (F : 类型) (M N : outParam 类型)
  公理与运算 (2 个):
    - map_fun : 对任意 (φ : F) {n} (f : L.函数 n) (x), φ (funMap f x) = funMap f (φ ∘ x)
    - map_rel : 对任意 (φ : F) {n} (r : L.关系 n) (x), RelMap r (φ ∘ x) ↔ RelMap r x
-/
class StrongHomClass (L : outParam Language) (F : Type*) (M N : outParam Type*)
  [FunLike F M N] [L.Structure M] [L.Structure N] : Prop where
  map_fun : forall (φ : F) {n} (f : L.Functions n) (x), φ (funMap f x) = funMap f (φ ∘ x)
  map_rel : forall (φ : F) {n} (r : L.Relations n) (x), RelMap r (φ ∘ x) ↔ RelMap r x

instance (priority := 100) StrongHomClass.homClass {F : Type*}
    [FunLike F M N] [StrongHomClass L F M N] : HomClass L F M N where
  map_fun := StrongHomClass.map_fun
  map_rel φ _ R x := (StrongHomClass.map_rel φ R x).2

/--
theorem `HomClass.strongHomClassOfIsAlgebraic` / 定理 `HomClass.strongHomClassOfIsAlgebraic`

English:
theorem HomClass.strongHomClassOfIsAlgebraic
  statement: [L.IsAlgebraic] {F M N} [L.Structure M] [L.Structure N]
  proof: HomClass.map_fun
  map_rel _ _ := isEmptyElim

中文:
定理 态射类.strongHomClassOfIsAlgebraic
  结论: [L.是代数] {F M N} [L.结构 M] [L.结构 N]
  证明: HomClass.map_fun
  map_rel _ _ := isEmptyElim

Depends on / 依赖: HomClass, HomClass.map_fun, map_fun
-/
theorem HomClass.strongHomClassOfIsAlgebraic [L.IsAlgebraic] {F M N} [L.Structure M] [L.Structure N]
    [FunLike F M N] [HomClass L F M N] : StrongHomClass L F M N where
  map_fun := HomClass.map_fun
  map_rel _ _ := isEmptyElim

/--
theorem `HomClass.map_constants` / 定理 `HomClass.map_constants`

English:
theorem HomClass.map_constants
  statement: {F M N} [L.Structure M] [L.Structure N] [FunLike F M N]
  proof: (HomClass.map_fun φ c default).trans (congr rfl (funext default))

中文:
定理 态射类.map_constants
  结论: {F M N} [L.结构 M] [L.结构 N] [函数状 F M N]
  证明: (HomClass.map_fun φ c default).trans (congr rfl (funext default))

Depends on / 依赖: HomClass, HomClass.map_fun, map_fun
-/
theorem HomClass.map_constants {F M N} [L.Structure M] [L.Structure N] [FunLike F M N]
    [HomClass L F M N] (φ : F) (c : L.Constants) : φ c = c :=
  (HomClass.map_fun φ c default).trans (congr rfl (funext default))

attribute [inherit_doc FirstOrder.Language.Hom.map_fun'] FirstOrder.Language.Embedding.map_fun'
  FirstOrder.Language.HomClass.map_fun FirstOrder.Language.StrongHomClass.map_fun
  FirstOrder.Language.Equiv.map_fun'

attribute [inherit_doc FirstOrder.Language.Hom.map_rel'] FirstOrder.Language.Embedding.map_rel'
  FirstOrder.Language.HomClass.map_rel FirstOrder.Language.StrongHomClass.map_rel
  FirstOrder.Language.Equiv.map_rel'

namespace Hom

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (M ->[L] N) M N where
  body: Hom.toFun
  coe_injective f g h := by cases f; cases g; cases h; rfl

中文:
实例 instFunLike
  签名: : 函数状 (M ->[L] N) M N where
  定义体: Hom.toFun
  coe_injective f g h := by cases f; cases g; cases h; rfl

Depends on / 依赖: Hom.toFun
-/
instance instFunLike : FunLike (M ->[L] N) M N where
  coe := Hom.toFun
  coe_injective f g h := by cases f; cases g; cases h; rfl

/--
Instance `homClass` / 实例 `homClass`

English:
instance homClass
  signature: : HomClass L (M ->[L] N) M N where
  body: map_fun'
  map_rel := map_rel'

中文:
实例 homClass
  签名: : 态射类 L (M ->[L] N) M N where
  定义体: map_fun'
  map_rel := map_rel'

Depends on / 依赖: map_fun
-/
instance homClass : HomClass L (M ->[L] N) M N where
  map_fun := map_fun'
  map_rel := map_rel'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [L.IsAlgebraic]
  signature: : StrongHomClass L (M ->[L] N) M N
  body: HomClass.strongHomClassOfIsAlgebraic

@[simp]

中文:
实例 [L.是代数]
  签名: : Strong态射类 L (M ->[L] N) M N
  定义体: HomClass.strongHomClassOfIsAlgebraic

@[simp]

Depends on / 依赖: HomClass, HomClass.strongHomClassOfIsAlgebraic, strongHomClassOfIsAlgebraic
-/
instance [L.IsAlgebraic] : StrongHomClass L (M ->[L] N) M N :=
  HomClass.strongHomClassOfIsAlgebraic

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: {f : M ->[L] N}
  statement: f.toFun = (f : M -> N)
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe
  条件: {f : M ->[L] N}
  结论: f.toFun = (f : M -> N)
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe {f : M ->[L] N} : f.toFun = (f : M -> N) :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: M ->[L] N⦄ (h : forall x, f x = g x) : f = g
  proof: DFunLike.ext f g h

@[simp]

中文:
定理 ext
  条件: ⦃f g
  结论: M ->[L] N⦄ (h : 对任意 x, f x = g x) : f = g
  证明: DFunLike.ext f g h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext ⦃f g : M ->[L] N⦄ (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
/--
theorem `map_fun` / 定理 `map_fun`

English:
theorem map_fun
  given: (φ : M ->[L] N) {n : Nat} (f : L.Functions n) (x : Fin n -> M)
  proof: HomClass.map_fun φ f x

@[simp]

中文:
定理 map_fun
  条件: (φ : M ->[L] N) {n : 自然数} (f : L.函数 n) (x : 有限集 n -> M)
  证明: HomClass.map_fun φ f x

@[simp]

Depends on / 依赖: HomClass, HomClass.map_fun, map_fun
-/
theorem map_fun (φ : M ->[L] N) {n : Nat} (f : L.Functions n) (x : Fin n -> M) :
    φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x

@[simp]
/--
theorem `map_constants` / 定理 `map_constants`

English:
theorem map_constants
  given: (φ : M ->[L] N) (c : L.Constants)
  statement: φ c = c
  proof: HomClass.map_constants φ c

@[simp]

中文:
定理 map_constants
  条件: (φ : M ->[L] N) (c : L.Constants)
  结论: φ c = c
  证明: HomClass.map_constants φ c

@[simp]

Depends on / 依赖: HomClass, HomClass.map_constants, map_constants
-/
theorem map_constants (φ : M ->[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c

@[simp]
/--
theorem `map_rel` / 定理 `map_rel`

English:
theorem map_rel
  given: (φ : M ->[L] N) {n : Nat} (r : L.Relations n) (x : Fin n -> M)
  proof: HomClass.map_rel φ r x

中文:
定理 map_rel
  条件: (φ : M ->[L] N) {n : 自然数} (r : L.关系 n) (x : 有限集 n -> M)
  证明: HomClass.map_rel φ r x

Depends on / 依赖: HomClass, HomClass.map_rel, map_rel
-/
theorem map_rel (φ : M ->[L] N) {n : Nat} (r : L.Relations n) (x : Fin n -> M) :
    RelMap r x -> RelMap r (φ ∘ x) :=
  HomClass.map_rel φ r x

variable (L) (M)

/-- The identity map from a structure to itself. -/
@[refl]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : M ->[L] M where
  body: m

中文:
定义 id
  签名: : M ->[L] M where
  定义体: m
-/
def id : M ->[L] M where
  toFun m := m

variable {L} {M}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (M ->[L] M)
  body: ⟨id L M⟩

@[simp]

中文:
实例 :
  签名: 可居 (M ->[L] M)
  定义体: ⟨id L M⟩

@[simp]
-/
instance : Inhabited (M ->[L] M) :=
  ⟨id L M⟩

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (x : M)
  statement: id L M x = x
  proof: rfl

中文:
定理 id_apply
  条件: (x : M)
  结论: id L M x = x
  证明: rfl
-/
theorem id_apply (x : M) : id L M x = x :=
  rfl

/-- Composition of first-order homomorphisms. -/
@[trans]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (hnp : N ->[L] P) (hmn : M ->[L] N)
  body: hnp ∘ hmn
  -- Porting note: should be done by autoparam?
  map_fun' _ _ := by simp; rfl
  -- Porting note: should be done by autoparam?
  map_rel' _ _ h := map_rel _ _ _ (map_rel _ _ _ h)

@[simp]

中文:
定义 comp
  签名: (hnp : N ->[L] P) (hmn : M ->[L] N)
  定义体: hnp ∘ hmn
  -- Porting note: should be done by autoparam?
  map_fun' _ _ := by simp; rfl
  -- Porting note: should be done by autoparam?
  map_rel' _ _ h := map_rel _ _ _ (map_rel _ _ _ h)

@[simp]
-/
def comp (hnp : N ->[L] P) (hmn : M ->[L] N) : M ->[L] P where
  toFun := hnp ∘ hmn
  -- Porting note: should be done by autoparam?
  map_fun' _ _ := by simp; rfl
  -- Porting note: should be done by autoparam?
  map_rel' _ _ h := map_rel _ _ _ (map_rel _ _ _ h)

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (g : N ->[L] P) (f : M ->[L] N) (x : M)
  statement: g.comp f x = g (f x)
  proof: rfl

中文:
定理 comp_apply
  条件: (g : N ->[L] P) (f : M ->[L] N) (x : M)
  结论: g.comp f x = g (f x)
  证明: rfl
-/
theorem comp_apply (g : N ->[L] P) (f : M ->[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : M ->[L] N) (g : N ->[L] P) (h : P ->[L] Q)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : M ->[L] N) (g : N ->[L] P) (h : P ->[L] Q)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : M ->[L] N) (g : N ->[L] P) (h : P ->[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : M ->[L] N)
  statement: f.comp (id L M) = f
  proof: rfl

@[simp]

中文:
定理 comp_id
  条件: (f : M ->[L] N)
  结论: f.comp (id L M) = f
  证明: rfl

@[simp]
-/
theorem comp_id (f : M ->[L] N) : f.comp (id L M) = f :=
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : M ->[L] N)
  statement: (id L N).comp f = f
  proof: rfl

中文:
定理 id_comp
  条件: (f : M ->[L] N)
  结论: (id L N).comp f = f
  证明: rfl
-/
theorem id_comp (f : M ->[L] N) : (id L N).comp f = f :=
  rfl

end Hom

/--
Definition of `HomClass.toHom` / `HomClass.toHom` 的定义

English:
definition HomClass.toHom
  signature: {F M N} [L.Structure M] [L.Structure N] [FunLike F M N]
  body: fun φ =>
  ⟨φ, HomClass.map_fun φ, HomClass.map_rel φ⟩

中文:
定义 态射类.toHom
  签名: {F M N} [L.结构 M] [L.结构 N] [函数状 F M N]
  定义体: fun φ =>
  ⟨φ, HomClass.map_fun φ, HomClass.map_rel φ⟩
-/
@[simps] def HomClass.toHom {F M N} [L.Structure M] [L.Structure N] [FunLike F M N]
    [HomClass L F M N] : F -> M ->[L] N := fun φ =>
  ⟨φ, HomClass.map_fun φ, HomClass.map_rel φ⟩

namespace Embedding

/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (M ↪[L] N) M N where
  body: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact funext_iff.1 h x

中文:
实例 funLike
  签名: : 函数状 (M ↪[L] N) M N where
  定义体: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact funext_iff.1 h x

Depends on / 依赖: f.toFun
-/
instance funLike : FunLike (M ↪[L] N) M N where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact funext_iff.1 h x

/--
Instance `embeddingLike` / 实例 `embeddingLike`

English:
instance embeddingLike
  signature: : EmbeddingLike (M ↪[L] N) M N where
  body: f.toEmbedding.injective

中文:
实例 embeddingLike
  签名: : EmbeddingLike (M ↪[L] N) M N where
  定义体: f.toEmbedding.injective

Depends on / 依赖: f.toEmbedding.injective, injective, toEmbedding
-/
instance embeddingLike : EmbeddingLike (M ↪[L] N) M N where
  injective' f := f.toEmbedding.injective

/--
Instance `strongHomClass` / 实例 `strongHomClass`

English:
instance strongHomClass
  signature: : StrongHomClass L (M ↪[L] N) M N where
  body: map_fun'
  map_rel := map_rel'

@[simp]

中文:
实例 strongHomClass
  签名: : Strong态射类 L (M ↪[L] N) M N where
  定义体: map_fun'
  map_rel := map_rel'

@[simp]

Depends on / 依赖: map_fun
-/
instance strongHomClass : StrongHomClass L (M ↪[L] N) M N where
  map_fun := map_fun'
  map_rel := map_rel'

@[simp]
/--
theorem `map_fun` / 定理 `map_fun`

English:
theorem map_fun
  given: (φ : M ↪[L] N) {n : Nat} (f : L.Functions n) (x : Fin n -> M)
  proof: HomClass.map_fun φ f x

@[simp]

中文:
定理 map_fun
  条件: (φ : M ↪[L] N) {n : 自然数} (f : L.函数 n) (x : 有限集 n -> M)
  证明: HomClass.map_fun φ f x

@[simp]

Depends on / 依赖: HomClass, HomClass.map_fun, map_fun
-/
theorem map_fun (φ : M ↪[L] N) {n : Nat} (f : L.Functions n) (x : Fin n -> M) :
    φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x

@[simp]
/--
theorem `map_constants` / 定理 `map_constants`

English:
theorem map_constants
  given: (φ : M ↪[L] N) (c : L.Constants)
  statement: φ c = c
  proof: HomClass.map_constants φ c

@[simp]

中文:
定理 map_constants
  条件: (φ : M ↪[L] N) (c : L.Constants)
  结论: φ c = c
  证明: HomClass.map_constants φ c

@[simp]

Depends on / 依赖: HomClass, HomClass.map_constants, map_constants
-/
theorem map_constants (φ : M ↪[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c

@[simp]
/--
theorem `map_rel` / 定理 `map_rel`

English:
theorem map_rel
  given: (φ : M ↪[L] N) {n : Nat} (r : L.Relations n) (x : Fin n -> M)
  proof: StrongHomClass.map_rel φ r x

中文:
定理 map_rel
  条件: (φ : M ↪[L] N) {n : 自然数} (r : L.关系 n) (x : 有限集 n -> M)
  证明: StrongHomClass.map_rel φ r x

Depends on / 依赖: StrongHomClass, StrongHomClass.map_rel, map_rel
-/
theorem map_rel (φ : M ↪[L] N) {n : Nat} (r : L.Relations n) (x : Fin n -> M) :
    RelMap r (φ ∘ x) ↔ RelMap r x :=
  StrongHomClass.map_rel φ r x

/--
Definition of `toHom` / `toHom` 的定义

English:
definition toHom
  signature: : (M ↪[L] N) -> M ->[L] N
  body: HomClass.toHom

@[simp]

中文:
定义 toHom
  签名: : (M ↪[L] N) -> M ->[L] N
  定义体: HomClass.toHom

@[simp]

Depends on / 依赖: HomClass, HomClass.toHom
-/
def toHom : (M ↪[L] N) -> M ->[L] N :=
  HomClass.toHom

@[simp]
/--
theorem `coe_toHom` / 定理 `coe_toHom`

English:
theorem coe_toHom
  given: {f : M ↪[L] N}
  statement: (f.toHom : M -> N) = f
  proof: rfl

中文:
定理 coe_toHom
  条件: {f : M ↪[L] N}
  结论: (f.toHom : M -> N) = f
  证明: rfl
-/
theorem coe_toHom {f : M ↪[L] N} : (f.toHom : M -> N) = f :=
  rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: @Function.Injective (M ↪[L] N) (M -> N) (↑)

中文:
定理 coe_injective
  结论: @函数.单射 (M ↪[L] N) (M -> N) (↑)
-/
theorem coe_injective : @Function.Injective (M ↪[L] N) (M -> N) (↑)
  | _, _, h => DFunLike.ext'_iff.mpr h

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: M ↪[L] N⦄ (h : forall x, f x = g x) : f = g
  proof: coe_injective (funext h)

中文:
定理 ext
  条件: ⦃f g
  结论: M ↪[L] N⦄ (h : 对任意 x, f x = g x) : f = g
  证明: coe_injective (funext h)

Depends on / 依赖: coe_injective
-/
theorem ext ⦃f g : M ↪[L] N⦄ (h : forall x, f x = g x) : f = g :=
  coe_injective (funext h)

/--
theorem `toHom_injective` / 定理 `toHom_injective`

English:
theorem toHom_injective
  statement: @Function.Injective (M ↪[L] N) (M ->[L] N) (·.toHom)
  proof: by
  intro f f' h
  ext
  exact congr_fun (congr_arg (↑) h) _

@[simp]

中文:
定理 toHom_injective
  结论: @函数.单射 (M ↪[L] N) (M ->[L] N) (·.toHom)
  证明: by
  intro f f' h
  ext
  exact congr_fun (congr_arg (↑) h) _

@[simp]

Depends on / 依赖: congr_arg, congr_fun
-/
theorem toHom_injective : @Function.Injective (M ↪[L] N) (M ->[L] N) (·.toHom) := by
  intro f f' h
  ext
  exact congr_fun (congr_arg (↑) h) _

@[simp]
/--
theorem `toHom_inj` / 定理 `toHom_inj`

English:
theorem toHom_inj
  given: {f g : M ↪[L] N}
  statement: f.toHom = g.toHom ↔ f = g
  proof: ⟨fun h => toHom_injective h, fun h => congr_arg (·.toHom) h⟩

中文:
定理 toHom_inj
  条件: {f g : M ↪[L] N}
  结论: f.toHom = g.toHom ↔ f = g
  证明: ⟨fun h => toHom_injective h, fun h => congr_arg (·.toHom) h⟩

Depends on / 依赖: congr_arg, toHom_injective
-/
theorem toHom_inj {f g : M ↪[L] N} : f.toHom = g.toHom ↔ f = g :=
  ⟨fun h => toHom_injective h, fun h => congr_arg (·.toHom) h⟩

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (f : M ↪[L] N)
  statement: Function.Injective f
  proof: f.toEmbedding.injective

中文:
定理 injective
  条件: (f : M ↪[L] N)
  结论: 函数.单射 f
  证明: f.toEmbedding.injective

Depends on / 依赖: f.toEmbedding.injective, injective, toEmbedding
-/
theorem injective (f : M ↪[L] N) : Function.Injective f :=
  f.toEmbedding.injective

/-- In an algebraic language, any injective homomorphism is an embedding. -/
@[simps!]
/--
Definition of `ofInjective` / `ofInjective` 的定义

English:
definition ofInjective
  signature: [L.IsAlgebraic] {f : M ->[L] N} (hf : Function.Injective f)
  body: { f with
    inj' := hf
    map_rel' := fun {_} r x => StrongHomClass.map_rel f r x }

@[simp]

中文:
定义 ofInjective
  签名: [L.是代数] {f : M ->[L] N} (hf : 函数.单射 f)
  定义体: { f with
    inj' := hf
    map_rel' := fun {_} r x => StrongHomClass.map_rel f r x }

@[simp]

Depends on / 依赖: StrongHomClass, StrongHomClass.map_rel, map_rel
-/
def ofInjective [L.IsAlgebraic] {f : M ->[L] N} (hf : Function.Injective f) : M ↪[L] N :=
  { f with
    inj' := hf
    map_rel' := fun {_} r x => StrongHomClass.map_rel f r x }

@[simp]
/--
theorem `coeFn_ofInjective` / 定理 `coeFn_ofInjective`

English:
theorem coeFn_ofInjective
  given: [L.IsAlgebraic] {f : M ->[L] N} (hf : Function.Injective f)
  proof: rfl

@[simp]

中文:
定理 coeFn_ofInjective
  条件: [L.是代数] {f : M ->[L] N} (hf : 函数.单射 f)
  证明: rfl

@[simp]
-/
theorem coeFn_ofInjective [L.IsAlgebraic] {f : M ->[L] N} (hf : Function.Injective f) :
    (ofInjective hf : M -> N) = f :=
  rfl

@[simp]
/--
theorem `ofInjective_toHom` / 定理 `ofInjective_toHom`

English:
theorem ofInjective_toHom
  given: [L.IsAlgebraic] {f : M ->[L] N} (hf : Function.Injective f)
  proof: by
  ext; simp

中文:
定理 ofInjective_toHom
  条件: [L.是代数] {f : M ->[L] N} (hf : 函数.单射 f)
  证明: by
  ext; simp
-/
theorem ofInjective_toHom [L.IsAlgebraic] {f : M ->[L] N} (hf : Function.Injective f) :
    (ofInjective hf).toHom = f := by
  ext; simp

variable (L) (M)

/-- The identity embedding from a structure to itself. -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : M ↪[L] M where toEmbedding
  body: Function.Embedding.refl M

中文:
定义 refl
  签名: : M ↪[L] M where toEmbedding
  定义体: Function.Embedding.refl M

Depends on / 依赖: Embedding, Function, Function.Embedding.refl
-/
def refl : M ↪[L] M where toEmbedding := Function.Embedding.refl M

variable {L} {M}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (M ↪[L] M)
  body: ⟨refl L M⟩

@[simp]

中文:
实例 :
  签名: 可居 (M ↪[L] M)
  定义体: ⟨refl L M⟩

@[simp]
-/
instance : Inhabited (M ↪[L] M) :=
  ⟨refl L M⟩

@[simp]
/--
theorem `refl_apply` / 定理 `refl_apply`

English:
theorem refl_apply
  given: (x : M)
  statement: refl L M x = x
  proof: rfl

中文:
定理 refl_apply
  条件: (x : M)
  结论: refl L M x = x
  证明: rfl
-/
theorem refl_apply (x : M) : refl L M x = x :=
  rfl

/-- Composition of first-order embeddings. -/
@[trans]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (hnp : N ↪[L] P) (hmn : M ↪[L] N)
  body: hnp ∘ hmn
  inj' := hnp.injective.comp hmn.injective
  -- Porting note: should be done by autoparam?
  map_fun' := by intros; simp only [Function.comp_apply, map_fun]; trivial
  -- Porting note: should be done by autoparam?
  map_rel' := by intros; rw [Function.comp_assoc, map_rel, map_rel]

@[simp]

中文:
定义 comp
  签名: (hnp : N ↪[L] P) (hmn : M ↪[L] N)
  定义体: hnp ∘ hmn
  inj' := hnp.injective.comp hmn.injective
  -- Porting note: should be done by autoparam?
  map_fun' := by intros; simp only [Function.comp_apply, map_fun]; trivial
  -- Porting note: should be done by autoparam?
  map_rel' := by intros; rw [Function.comp_assoc, map_rel, map_rel]

@[simp]
-/
def comp (hnp : N ↪[L] P) (hmn : M ↪[L] N) : M ↪[L] P where
  toFun := hnp ∘ hmn
  inj' := hnp.injective.comp hmn.injective
  -- Porting note: should be done by autoparam?
  map_fun' := by intros; simp only [Function.comp_apply, map_fun]; trivial
  -- Porting note: should be done by autoparam?
  map_rel' := by intros; rw [Function.comp_assoc, map_rel, map_rel]

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (g : N ↪[L] P) (f : M ↪[L] N) (x : M)
  statement: g.comp f x = g (f x)
  proof: rfl

中文:
定理 comp_apply
  条件: (g : N ↪[L] P) (f : M ↪[L] N) (x : M)
  结论: g.comp f x = g (f x)
  证明: rfl
-/
theorem comp_apply (g : N ↪[L] P) (f : M ↪[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q)
  proof: rfl

中文:
定理 comp_assoc
  条件: (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q)
  证明: rfl
-/
theorem comp_assoc (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

/--
theorem `comp_injective` / 定理 `comp_injective`

English:
theorem comp_injective
  given: (h : N ↪[L] P)
  proof: by
  intro f g hfg
  ext x; exact h.injective (DFunLike.congr_fun hfg x)

@[simp]

中文:
定理 comp_injective
  条件: (h : N ↪[L] P)
  证明: by
  intro f g hfg
  ext x; exact h.injective (DFunLike.congr_fun hfg x)

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, h.injective, injective
-/
theorem comp_injective (h : N ↪[L] P) :
    Function.Injective (h.comp : (M ↪[L] N) -> (M ↪[L] P)) := by
  intro f g hfg
  ext x; exact h.injective (DFunLike.congr_fun hfg x)

@[simp]
/--
theorem `comp_inj` / 定理 `comp_inj`

English:
theorem comp_inj
  given: (h : N ↪[L] P) (f g : M ↪[L] N)
  statement: h.comp f = h.comp g ↔ f = g
  proof: ⟨fun eq => h.comp_injective eq, congr_arg h.comp⟩

中文:
定理 comp_inj
  条件: (h : N ↪[L] P) (f g : M ↪[L] N)
  结论: h.comp f = h.comp g ↔ f = g
  证明: ⟨fun eq => h.comp_injective eq, congr_arg h.comp⟩

Depends on / 依赖: comp_injective, congr_arg, h.comp, h.comp_injective
-/
theorem comp_inj (h : N ↪[L] P) (f g : M ↪[L] N) : h.comp f = h.comp g ↔ f = g :=
  ⟨fun eq => h.comp_injective eq, congr_arg h.comp⟩

/--
theorem `toHom_comp_injective` / 定理 `toHom_comp_injective`

English:
theorem toHom_comp_injective
  given: (h : N ↪[L] P)
  proof: by
  intro f g hfg
  ext x; exact h.injective (DFunLike.congr_fun hfg x)

@[simp]

中文:
定理 toHom_comp_injective
  条件: (h : N ↪[L] P)
  证明: by
  intro f g hfg
  ext x; exact h.injective (DFunLike.congr_fun hfg x)

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, h.injective, injective
-/
theorem toHom_comp_injective (h : N ↪[L] P) :
    Function.Injective (h.toHom.comp : (M ->[L] N) -> (M ->[L] P)) := by
  intro f g hfg
  ext x; exact h.injective (DFunLike.congr_fun hfg x)

@[simp]
/--
theorem `toHom_comp_inj` / 定理 `toHom_comp_inj`

English:
theorem toHom_comp_inj
  given: (h : N ↪[L] P) (f g : M ->[L] N)
  statement: h.toHom.comp f = h.toHom.comp g ↔ f = g
  proof: ⟨fun eq => h.toHom_comp_injective eq, congr_arg h.toHom.comp⟩

@[simp]

中文:
定理 toHom_comp_inj
  条件: (h : N ↪[L] P) (f g : M ->[L] N)
  结论: h.toHom.comp f = h.toHom.comp g ↔ f = g
  证明: ⟨fun eq => h.toHom_comp_injective eq, congr_arg h.toHom.comp⟩

@[simp]

Depends on / 依赖: congr_arg, h.toHom.comp, h.toHom_comp_injective, toHom_comp_injective
-/
theorem toHom_comp_inj (h : N ↪[L] P) (f g : M ->[L] N) : h.toHom.comp f = h.toHom.comp g ↔ f = g :=
  ⟨fun eq => h.toHom_comp_injective eq, congr_arg h.toHom.comp⟩

@[simp]
/--
theorem `comp_toHom` / 定理 `comp_toHom`

English:
theorem comp_toHom
  given: (hnp : N ↪[L] P) (hmn : M ↪[L] N)
  proof: rfl

@[simp]

中文:
定理 comp_toHom
  条件: (hnp : N ↪[L] P) (hmn : M ↪[L] N)
  证明: rfl

@[simp]
-/
theorem comp_toHom (hnp : N ↪[L] P) (hmn : M ↪[L] N) :
    (hnp.comp hmn).toHom = hnp.toHom.comp hmn.toHom :=
  rfl

@[simp]
/--
theorem `comp_refl` / 定理 `comp_refl`

English:
theorem comp_refl
  given: (f : M ↪[L] N)
  statement: f.comp (refl L M) = f
  proof: DFunLike.coe_injective rfl

@[simp]

中文:
定理 comp_refl
  条件: (f : M ↪[L] N)
  结论: f.comp (refl L M) = f
  证明: DFunLike.coe_injective rfl

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem comp_refl (f : M ↪[L] N) : f.comp (refl L M) = f := DFunLike.coe_injective rfl

@[simp]
/--
theorem `refl_comp` / 定理 `refl_comp`

English:
theorem refl_comp
  given: (f : M ↪[L] N)
  statement: (refl L N).comp f = f
  proof: DFunLike.coe_injective rfl

@[simp]

中文:
定理 refl_comp
  条件: (f : M ↪[L] N)
  结论: (refl L N).comp f = f
  证明: DFunLike.coe_injective rfl

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem refl_comp (f : M ↪[L] N) : (refl L N).comp f = f := DFunLike.coe_injective rfl

@[simp]
/--
theorem `refl_toHom` / 定理 `refl_toHom`

English:
theorem refl_toHom
  statement: (refl L M).toHom = Hom.id L M
  proof: rfl

中文:
定理 refl_toHom
  结论: (refl L M).toHom = 态射.id L M
  证明: rfl
-/
theorem refl_toHom : (refl L M).toHom = Hom.id L M :=
  rfl

end Embedding

/--
Definition of `StrongHomClass.toEmbedding` / `StrongHomClass.toEmbedding` 的定义

English:
definition StrongHomClass.toEmbedding
  signature: {F M N} [L.Structure M] [L.Structure N] [FunLike F M N]
  body: fun φ =>
  ⟨⟨φ, EmbeddingLike.injective φ⟩, StrongHomClass.map_fun φ, StrongHomClass.map_rel φ⟩

中文:
定义 Strong态射类.toEmbedding
  签名: {F M N} [L.结构 M] [L.结构 N] [函数状 F M N]
  定义体: fun φ =>
  ⟨⟨φ, EmbeddingLike.injective φ⟩, StrongHomClass.map_fun φ, StrongHomClass.map_rel φ⟩
-/
@[simps] def StrongHomClass.toEmbedding {F M N} [L.Structure M] [L.Structure N] [FunLike F M N]
    [EmbeddingLike F M N] [StrongHomClass L F M N] : F -> M ↪[L] N := fun φ =>
  ⟨⟨φ, EmbeddingLike.injective φ⟩, StrongHomClass.map_fun φ, StrongHomClass.map_rel φ⟩

namespace Equiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (M ≃[L] N) M N
  body: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    simp only [mk.injEq]
    ext x
    exact funext_iff.1 h₁ x

中文:
实例 :
  签名: 等价状 (M ≃[L] N) M N
  定义体: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    simp only [mk.injEq]
    ext x
    exact funext_iff.1 h₁ x

Depends on / 依赖: f.toFun
-/
instance : EquivLike (M ≃[L] N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    simp only [mk.injEq]
    ext x
    exact funext_iff.1 h₁ x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StrongHomClass L (M ≃[L] N) M N
  body: map_fun'
  map_rel := map_rel'

中文:
实例 :
  签名: Strong态射类 L (M ≃[L] N) M N
  定义体: map_fun'
  map_rel := map_rel'

Depends on / 依赖: map_fun
-/
instance : StrongHomClass L (M ≃[L] N) M N where
  map_fun := map_fun'
  map_rel := map_rel'

/-- The inverse of a first-order equivalence is a first-order equivalence. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (f : M ≃[L] N)
  body: { f.toEquiv.symm with
    map_fun' := fun n f' {x} => by
      simp only [Equiv.toFun_as_coe]
      rw [Equiv.symm_apply_eq]
      refine Eq.trans ?_ (f.map_fun' f' (f.toEquiv.symm ∘ x)).symm
      rw [← Function.comp_assoc]; rw [Equiv.toFun_as_coe]; rw [Equiv.self_comp_symm]; rw [Function.id_comp]


中文:
定义 symm
  签名: (f : M ≃[L] N)
  定义体: { f.toEquiv.symm with
    map_fun' := fun n f' {x} => by
      simp only [Equiv.toFun_as_coe]
      rw [Equiv.symm_apply_eq]
      refine Eq.trans ?_ (f.map_fun' f' (f.toEquiv.symm ∘ x)).symm
      rw [← Function.comp_assoc]; rw [Equiv.toFun_as_coe]; rw [Equiv.self_comp_symm]; rw [Function.id_comp]


Depends on / 依赖: Eq.trans, Equiv.self_comp_symm, Equiv.symm_apply_eq, Equiv.toFun_as_coe, Function, Function.comp_assoc, Function.id_comp, comp_assoc, f.map_fun, f.map_rel, f.toEquiv.symm, id_comp, map_fun, map_rel, self_comp_symm, symm.trans, symm_apply_eq, toEquiv, toFun_as_coe
-/
def symm (f : M ≃[L] N) : N ≃[L] M :=
  { f.toEquiv.symm with
    map_fun' := fun n f' {x} => by
      simp only [Equiv.toFun_as_coe]
      rw [Equiv.symm_apply_eq]
      refine Eq.trans ?_ (f.map_fun' f' (f.toEquiv.symm ∘ x)).symm
      rw [← Function.comp_assoc]; rw [Equiv.toFun_as_coe]; rw [Equiv.self_comp_symm]; rw [Function.id_comp]
    map_rel' := fun n r {x} => by
      simp only [Equiv.toFun_as_coe]
      refine (f.map_rel' r (f.toEquiv.symm ∘ x)).symm.trans ?_
      rw [← Function.comp_assoc]; rw [Equiv.toFun_as_coe]; rw [Equiv.self_comp_symm]; rw [Function.id_comp] }

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (f : M ≃[L] N)
  proof: rfl

中文:
定理 symm_symm
  条件: (f : M ≃[L] N)
  证明: rfl
-/
theorem symm_symm (f : M ≃[L] N) :
    f.symm.symm = f :=
  rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (symm : (M ≃[L] N) -> _)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

中文:
定理 symm_bijective
  结论: 函数.双射 (symm : (M ≃[L] N) -> _)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (symm : (M ≃[L] N) -> _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (f : M ≃[L] N) (a : N)
  statement: f (f.symm a) = a
  proof: f.toEquiv.apply_symm_apply a

@[simp]

中文:
定理 apply_symm_apply
  条件: (f : M ≃[L] N) (a : N)
  结论: f (f.symm a) = a
  证明: f.toEquiv.apply_symm_apply a

@[simp]

Depends on / 依赖: apply_symm_apply, f.toEquiv.apply_symm_apply, toEquiv
-/
theorem apply_symm_apply (f : M ≃[L] N) (a : N) : f (f.symm a) = a :=
  f.toEquiv.apply_symm_apply a

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (f : M ≃[L] N) (a : M)
  statement: f.symm (f a) = a
  proof: f.toEquiv.symm_apply_apply a

@[simp]

中文:
定理 symm_apply_apply
  条件: (f : M ≃[L] N) (a : M)
  结论: f.symm (f a) = a
  证明: f.toEquiv.symm_apply_apply a

@[simp]

Depends on / 依赖: f.toEquiv.symm_apply_apply, symm_apply_apply, toEquiv
-/
theorem symm_apply_apply (f : M ≃[L] N) (a : M) : f.symm (f a) = a :=
  f.toEquiv.symm_apply_apply a

@[simp]
/--
theorem `map_fun` / 定理 `map_fun`

English:
theorem map_fun
  given: (φ : M ≃[L] N) {n : Nat} (f : L.Functions n) (x : Fin n -> M)
  proof: HomClass.map_fun φ f x

@[simp]

中文:
定理 map_fun
  条件: (φ : M ≃[L] N) {n : 自然数} (f : L.函数 n) (x : 有限集 n -> M)
  证明: HomClass.map_fun φ f x

@[simp]

Depends on / 依赖: HomClass, HomClass.map_fun, map_fun
-/
theorem map_fun (φ : M ≃[L] N) {n : Nat} (f : L.Functions n) (x : Fin n -> M) :
    φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x

@[simp]
/--
theorem `map_constants` / 定理 `map_constants`

English:
theorem map_constants
  given: (φ : M ≃[L] N) (c : L.Constants)
  statement: φ c = c
  proof: HomClass.map_constants φ c

@[simp]

中文:
定理 map_constants
  条件: (φ : M ≃[L] N) (c : L.Constants)
  结论: φ c = c
  证明: HomClass.map_constants φ c

@[simp]

Depends on / 依赖: HomClass, HomClass.map_constants, map_constants
-/
theorem map_constants (φ : M ≃[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c

@[simp]
/--
theorem `map_rel` / 定理 `map_rel`

English:
theorem map_rel
  given: (φ : M ≃[L] N) {n : Nat} (r : L.Relations n) (x : Fin n -> M)
  proof: StrongHomClass.map_rel φ r x

中文:
定理 map_rel
  条件: (φ : M ≃[L] N) {n : 自然数} (r : L.关系 n) (x : 有限集 n -> M)
  证明: StrongHomClass.map_rel φ r x

Depends on / 依赖: StrongHomClass, StrongHomClass.map_rel, map_rel
-/
theorem map_rel (φ : M ≃[L] N) {n : Nat} (r : L.Relations n) (x : Fin n -> M) :
    RelMap r (φ ∘ x) ↔ RelMap r x :=
  StrongHomClass.map_rel φ r x

/--
Definition of `toEmbedding` / `toEmbedding` 的定义

English:
definition toEmbedding
  signature: : (M ≃[L] N) -> M ↪[L] N
  body: StrongHomClass.toEmbedding

中文:
定义 toEmbedding
  签名: : (M ≃[L] N) -> M ↪[L] N
  定义体: StrongHomClass.toEmbedding

Depends on / 依赖: StrongHomClass, StrongHomClass.toEmbedding, toEmbedding
-/
def toEmbedding : (M ≃[L] N) -> M ↪[L] N :=
  StrongHomClass.toEmbedding

/--
Definition of `toHom` / `toHom` 的定义

English:
definition toHom
  signature: : (M ≃[L] N) -> M ->[L] N
  body: HomClass.toHom

@[simp]

中文:
定义 toHom
  签名: : (M ≃[L] N) -> M ->[L] N
  定义体: HomClass.toHom

@[simp]

Depends on / 依赖: HomClass, HomClass.toHom
-/
def toHom : (M ≃[L] N) -> M ->[L] N :=
  HomClass.toHom

@[simp]
/--
theorem `toEmbedding_toHom` / 定理 `toEmbedding_toHom`

English:
theorem toEmbedding_toHom
  given: (f : M ≃[L] N)
  statement: f.toEmbedding.toHom = f.toHom
  proof: rfl

@[simp]

中文:
定理 toEmbedding_toHom
  条件: (f : M ≃[L] N)
  结论: f.toEmbedding.toHom = f.toHom
  证明: rfl

@[simp]
-/
theorem toEmbedding_toHom (f : M ≃[L] N) : f.toEmbedding.toHom = f.toHom :=
  rfl

@[simp]
/--
theorem `coe_toHom` / 定理 `coe_toHom`

English:
theorem coe_toHom
  given: {f : M ≃[L] N}
  statement: (f.toHom : M -> N) = (f : M -> N)
  proof: rfl

@[simp]

中文:
定理 coe_toHom
  条件: {f : M ≃[L] N}
  结论: (f.toHom : M -> N) = (f : M -> N)
  证明: rfl

@[simp]
-/
theorem coe_toHom {f : M ≃[L] N} : (f.toHom : M -> N) = (f : M -> N) :=
  rfl

@[simp]
/--
theorem `coe_toEmbedding` / 定理 `coe_toEmbedding`

English:
theorem coe_toEmbedding
  given: (f : M ≃[L] N)
  statement: (f.toEmbedding : M -> N) = (f : M -> N)
  proof: rfl

中文:
定理 coe_toEmbedding
  条件: (f : M ≃[L] N)
  结论: (f.toEmbedding : M -> N) = (f : M -> N)
  证明: rfl
-/
theorem coe_toEmbedding (f : M ≃[L] N) : (f.toEmbedding : M -> N) = (f : M -> N) :=
  rfl

/--
theorem `injective_toEmbedding` / 定理 `injective_toEmbedding`

English:
theorem injective_toEmbedding
  statement: Function.Injective (toEmbedding : (M ≃[L] N) -> M ↪[L] N)
  proof: by
  intro _ _ h; apply DFunLike.coe_injective; exact congr_arg (DFunLike.coe ∘ Embedding.toHom) h

中文:
定理 injective_toEmbedding
  结论: 函数.单射 (toEmbedding : (M ≃[L] N) -> M ↪[L] N)
  证明: by
  intro _ _ h; apply DFunLike.coe_injective; exact congr_arg (DFunLike.coe ∘ Embedding.toHom) h

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Embedding, Embedding.toHom, coe_injective, congr_arg
-/
theorem injective_toEmbedding : Function.Injective (toEmbedding : (M ≃[L] N) -> M ↪[L] N) := by
  intro _ _ h; apply DFunLike.coe_injective; exact congr_arg (DFunLike.coe ∘ Embedding.toHom) h

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: @Function.Injective (M ≃[L] N) (M -> N) (↑)
  proof: DFunLike.coe_injective

@[ext]

中文:
定理 coe_injective
  结论: @函数.单射 (M ≃[L] N) (M -> N) (↑)
  证明: DFunLike.coe_injective

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_injective : @Function.Injective (M ≃[L] N) (M -> N) (↑) :=
  DFunLike.coe_injective

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: M ≃[L] N⦄ (h : forall x, f x = g x) : f = g
  proof: coe_injective (funext h)

中文:
定理 ext
  条件: ⦃f g
  结论: M ≃[L] N⦄ (h : 对任意 x, f x = g x) : f = g
  证明: coe_injective (funext h)

Depends on / 依赖: coe_injective
-/
theorem ext ⦃f g : M ≃[L] N⦄ (h : forall x, f x = g x) : f = g :=
  coe_injective (funext h)

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (f : M ≃[L] N)
  statement: Function.Bijective f
  proof: EquivLike.bijective f

中文:
定理 bijective
  条件: (f : M ≃[L] N)
  结论: 函数.双射 f
  证明: EquivLike.bijective f

Depends on / 依赖: EquivLike, EquivLike.bijective, bijective
-/
theorem bijective (f : M ≃[L] N) : Function.Bijective f :=
  EquivLike.bijective f

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (f : M ≃[L] N)
  statement: Function.Injective f
  proof: EquivLike.injective f

中文:
定理 injective
  条件: (f : M ≃[L] N)
  结论: 函数.单射 f
  证明: EquivLike.injective f

Depends on / 依赖: EquivLike, EquivLike.injective, injective
-/
theorem injective (f : M ≃[L] N) : Function.Injective f :=
  EquivLike.injective f

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (f : M ≃[L] N)
  statement: Function.Surjective f
  proof: EquivLike.surjective f

中文:
定理 surjective
  条件: (f : M ≃[L] N)
  结论: 函数.满射 f
  证明: EquivLike.surjective f

Depends on / 依赖: EquivLike, EquivLike.surjective, surjective
-/
theorem surjective (f : M ≃[L] N) : Function.Surjective f :=
  EquivLike.surjective f

variable (L) (M)

/-- The identity equivalence from a structure to itself. -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : M ≃[L] M where toEquiv
  body: _root_.Equiv.refl M

中文:
定义 refl
  签名: : M ≃[L] M where toEquiv
  定义体: _root_.Equiv.refl M

Depends on / 依赖: _root_, _root_.Equiv.refl
-/
def refl : M ≃[L] M where toEquiv := _root_.Equiv.refl M

variable {L} {M}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (M ≃[L] M)
  body: ⟨refl L M⟩

@[simp]

中文:
实例 :
  签名: 可居 (M ≃[L] M)
  定义体: ⟨refl L M⟩

@[simp]
-/
instance : Inhabited (M ≃[L] M) :=
  ⟨refl L M⟩

@[simp]
/--
theorem `refl_apply` / 定理 `refl_apply`

English:
theorem refl_apply
  given: (x : M)
  statement: refl L M x = x
  proof: by simp [refl]; rfl

中文:
定理 refl_apply
  条件: (x : M)
  结论: refl L M x = x
  证明: by simp [refl]; rfl
-/
theorem refl_apply (x : M) : refl L M x = x := by simp [refl]; rfl

/-- Composition of first-order equivalences. -/
@[trans]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (hnp : N ≃[L] P) (hmn : M ≃[L] N)
  body: { hmn.toEquiv.trans hnp.toEquiv with
    toFun := hnp ∘ hmn
    -- Porting note: should be done by autoparam?
    map_fun' := by intros; simp only [Function.comp_apply, map_fun]; trivial
    -- Porting note: should be done by autoparam?
    map_rel' := by intros; rw [Function.comp_assoc, map_rel, ma

中文:
定义 comp
  签名: (hnp : N ≃[L] P) (hmn : M ≃[L] N)
  定义体: { hmn.toEquiv.trans hnp.toEquiv with
    toFun := hnp ∘ hmn
    -- Porting note: should be done by autoparam?
    map_fun' := by intros; simp only [Function.comp_apply, map_fun]; trivial
    -- Porting note: should be done by autoparam?
    map_rel' := by intros; rw [Function.comp_assoc, map_rel, ma

Depends on / 依赖: hmn.toEquiv.trans, hnp.toEquiv, toEquiv
-/
def comp (hnp : N ≃[L] P) (hmn : M ≃[L] N) : M ≃[L] P :=
  { hmn.toEquiv.trans hnp.toEquiv with
    toFun := hnp ∘ hmn
    -- Porting note: should be done by autoparam?
    map_fun' := by intros; simp only [Function.comp_apply, map_fun]; trivial
    -- Porting note: should be done by autoparam?
    map_rel' := by intros; rw [Function.comp_assoc, map_rel, map_rel] }

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (g : N ≃[L] P) (f : M ≃[L] N) (x : M)
  statement: g.comp f x = g (f x)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (g : N ≃[L] P) (f : M ≃[L] N) (x : M)
  结论: g.comp f x = g (f x)
  证明: rfl

@[simp]
-/
theorem comp_apply (g : N ≃[L] P) (f : M ≃[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

@[simp]
/--
theorem `comp_refl` / 定理 `comp_refl`

English:
theorem comp_refl
  given: (g : M ≃[L] N)
  statement: g.comp (refl L M) = g
  proof: rfl

@[simp]

中文:
定理 comp_refl
  条件: (g : M ≃[L] N)
  结论: g.comp (refl L M) = g
  证明: rfl

@[simp]
-/
theorem comp_refl (g : M ≃[L] N) : g.comp (refl L M) = g :=
  rfl

@[simp]
/--
theorem `refl_comp` / 定理 `refl_comp`

English:
theorem refl_comp
  given: (g : M ≃[L] N)
  statement: (refl L N).comp g = g
  proof: rfl

@[simp]

中文:
定理 refl_comp
  条件: (g : M ≃[L] N)
  结论: (refl L N).comp g = g
  证明: rfl

@[simp]
-/
theorem refl_comp (g : M ≃[L] N) : (refl L N).comp g = g :=
  rfl

@[simp]
/--
theorem `refl_toEmbedding` / 定理 `refl_toEmbedding`

English:
theorem refl_toEmbedding
  statement: (refl L M).toEmbedding = Embedding.refl L M
  proof: rfl

@[simp]

中文:
定理 refl_toEmbedding
  结论: (refl L M).toEmbedding = 嵌入.refl L M
  证明: rfl

@[simp]
-/
theorem refl_toEmbedding : (refl L M).toEmbedding = Embedding.refl L M :=
  rfl

@[simp]
/--
theorem `refl_toHom` / 定理 `refl_toHom`

English:
theorem refl_toHom
  statement: (refl L M).toHom = Hom.id L M
  proof: rfl

中文:
定理 refl_toHom
  结论: (refl L M).toHom = 态射.id L M
  证明: rfl
-/
theorem refl_toHom : (refl L M).toHom = Hom.id L M :=
  rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q)
  proof: rfl

中文:
定理 comp_assoc
  条件: (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q)
  证明: rfl
-/
theorem comp_assoc (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

/--
theorem `injective_comp` / 定理 `injective_comp`

English:
theorem injective_comp
  given: (h : N ≃[L] P)
  proof: by
  intro f g hfg
  ext x; exact h.injective (congr_fun (congr_arg DFunLike.coe hfg) x)

@[simp]

中文:
定理 injective_comp
  条件: (h : N ≃[L] P)
  证明: by
  intro f g hfg
  ext x; exact h.injective (congr_fun (congr_arg DFunLike.coe hfg) x)

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe, congr_arg, congr_fun, h.injective, injective
-/
theorem injective_comp (h : N ≃[L] P) :
    Function.Injective (h.comp : (M ≃[L] N) -> (M ≃[L] P)) := by
  intro f g hfg
  ext x; exact h.injective (congr_fun (congr_arg DFunLike.coe hfg) x)

@[simp]
/--
theorem `comp_toHom` / 定理 `comp_toHom`

English:
theorem comp_toHom
  given: (hnp : N ≃[L] P) (hmn : M ≃[L] N)
  proof: rfl

@[simp]

中文:
定理 comp_toHom
  条件: (hnp : N ≃[L] P) (hmn : M ≃[L] N)
  证明: rfl

@[simp]
-/
theorem comp_toHom (hnp : N ≃[L] P) (hmn : M ≃[L] N) :
    (hnp.comp hmn).toHom = hnp.toHom.comp hmn.toHom :=
  rfl

@[simp]
/--
theorem `comp_toEmbedding` / 定理 `comp_toEmbedding`

English:
theorem comp_toEmbedding
  given: (hnp : N ≃[L] P) (hmn : M ≃[L] N)
  proof: rfl

@[simp]

中文:
定理 comp_toEmbedding
  条件: (hnp : N ≃[L] P) (hmn : M ≃[L] N)
  证明: rfl

@[simp]
-/
theorem comp_toEmbedding (hnp : N ≃[L] P) (hmn : M ≃[L] N) :
    (hnp.comp hmn).toEmbedding = hnp.toEmbedding.comp hmn.toEmbedding :=
  rfl

@[simp]
/--
theorem `self_comp_symm` / 定理 `self_comp_symm`

English:
theorem self_comp_symm
  given: (f : M ≃[L] N)
  statement: f.comp f.symm = refl L N
  proof: by
  ext; rw [comp_apply, apply_symm_apply, refl_apply]

@[simp]

中文:
定理 self_comp_symm
  条件: (f : M ≃[L] N)
  结论: f.comp f.symm = refl L N
  证明: by
  ext; rw [comp_apply, apply_symm_apply, refl_apply]

@[simp]

Depends on / 依赖: apply_symm_apply, comp_apply, refl_apply
-/
theorem self_comp_symm (f : M ≃[L] N) : f.comp f.symm = refl L N := by
  ext; rw [comp_apply, apply_symm_apply, refl_apply]

@[simp]
/--
theorem `symm_comp_self` / 定理 `symm_comp_self`

English:
theorem symm_comp_self
  given: (f : M ≃[L] N)
  statement: f.symm.comp f = refl L M
  proof: by
  ext; rw [comp_apply, symm_apply_apply, refl_apply]

@[simp]

中文:
定理 symm_comp_self
  条件: (f : M ≃[L] N)
  结论: f.symm.comp f = refl L M
  证明: by
  ext; rw [comp_apply, symm_apply_apply, refl_apply]

@[simp]

Depends on / 依赖: comp_apply, refl_apply, symm_apply_apply
-/
theorem symm_comp_self (f : M ≃[L] N) : f.symm.comp f = refl L M := by
  ext; rw [comp_apply, symm_apply_apply, refl_apply]

@[simp]
/--
theorem `symm_comp_self_toEmbedding` / 定理 `symm_comp_self_toEmbedding`

English:
theorem symm_comp_self_toEmbedding
  given: (f : M ≃[L] N)
  proof: by
  rw [← comp_toEmbedding]; rw [symm_comp_self]; rw [refl_toEmbedding]

@[simp]

中文:
定理 symm_comp_self_toEmbedding
  条件: (f : M ≃[L] N)
  证明: by
  rw [← comp_toEmbedding]; rw [symm_comp_self]; rw [refl_toEmbedding]

@[simp]

Depends on / 依赖: comp_toEmbedding, refl_toEmbedding, symm_comp_self
-/
theorem symm_comp_self_toEmbedding (f : M ≃[L] N) :
    f.symm.toEmbedding.comp f.toEmbedding = Embedding.refl L M := by
  rw [← comp_toEmbedding]; rw [symm_comp_self]; rw [refl_toEmbedding]

@[simp]
/--
theorem `self_comp_symm_toEmbedding` / 定理 `self_comp_symm_toEmbedding`

English:
theorem self_comp_symm_toEmbedding
  given: (f : M ≃[L] N)
  proof: by
  rw [← comp_toEmbedding]; rw [self_comp_symm]; rw [refl_toEmbedding]

@[simp]

中文:
定理 self_comp_symm_toEmbedding
  条件: (f : M ≃[L] N)
  证明: by
  rw [← comp_toEmbedding]; rw [self_comp_symm]; rw [refl_toEmbedding]

@[simp]

Depends on / 依赖: comp_toEmbedding, refl_toEmbedding, self_comp_symm
-/
theorem self_comp_symm_toEmbedding (f : M ≃[L] N) :
    f.toEmbedding.comp f.symm.toEmbedding = Embedding.refl L N := by
  rw [← comp_toEmbedding]; rw [self_comp_symm]; rw [refl_toEmbedding]

@[simp]
/--
theorem `symm_comp_self_toHom` / 定理 `symm_comp_self_toHom`

English:
theorem symm_comp_self_toHom
  given: (f : M ≃[L] N)
  proof: by
  rw [← comp_toHom]; rw [symm_comp_self]; rw [refl_toHom]

@[simp]

中文:
定理 symm_comp_self_toHom
  条件: (f : M ≃[L] N)
  证明: by
  rw [← comp_toHom]; rw [symm_comp_self]; rw [refl_toHom]

@[simp]

Depends on / 依赖: comp_toHom, refl_toHom, symm_comp_self
-/
theorem symm_comp_self_toHom (f : M ≃[L] N) :
    f.symm.toHom.comp f.toHom = Hom.id L M := by
  rw [← comp_toHom]; rw [symm_comp_self]; rw [refl_toHom]

@[simp]
/--
theorem `self_comp_symm_toHom` / 定理 `self_comp_symm_toHom`

English:
theorem self_comp_symm_toHom
  given: (f : M ≃[L] N)
  proof: by
  rw [← comp_toHom]; rw [self_comp_symm]; rw [refl_toHom]

@[simp]

中文:
定理 self_comp_symm_toHom
  条件: (f : M ≃[L] N)
  证明: by
  rw [← comp_toHom]; rw [self_comp_symm]; rw [refl_toHom]

@[simp]

Depends on / 依赖: comp_toHom, refl_toHom, self_comp_symm
-/
theorem self_comp_symm_toHom (f : M ≃[L] N) :
    f.toHom.comp f.symm.toHom = Hom.id L N := by
  rw [← comp_toHom]; rw [self_comp_symm]; rw [refl_toHom]

@[simp]
/--
theorem `comp_symm` / 定理 `comp_symm`

English:
theorem comp_symm
  given: (f : M ≃[L] N) (g : N ≃[L] P)
  statement: (g.comp f).symm = f.symm.comp g.symm
  proof: rfl

中文:
定理 comp_symm
  条件: (f : M ≃[L] N) (g : N ≃[L] P)
  结论: (g.comp f).symm = f.symm.comp g.symm
  证明: rfl
-/
theorem comp_symm (f : M ≃[L] N) (g : N ≃[L] P) : (g.comp f).symm = f.symm.comp g.symm :=
  rfl

/--
theorem `comp_right_injective` / 定理 `comp_right_injective`

English:
theorem comp_right_injective
  given: (h : M ≃[L] N)
  proof: by
  intro f g hfg
  convert! (congr_arg (fun r : (M ≃[L] P) => r.comp h.symm) hfg) <;>
    rw [comp_assoc]; rw [self_comp_symm]; rw [comp_refl]

@[simp]

中文:
定理 comp_right_injective
  条件: (h : M ≃[L] N)
  证明: by
  intro f g hfg
  convert! (congr_arg (fun r : (M ≃[L] P) => r.comp h.symm) hfg) <;>
    rw [comp_assoc]; rw [self_comp_symm]; rw [comp_refl]

@[simp]

Depends on / 依赖: comp_assoc, comp_refl, congr_arg, convert, h.symm, r.comp, self_comp_symm
-/
theorem comp_right_injective (h : M ≃[L] N) :
    Function.Injective (fun f => f.comp h : (N ≃[L] P) -> (M ≃[L] P)) := by
  intro f g hfg
  convert! (congr_arg (fun r : (M ≃[L] P) => r.comp h.symm) hfg) <;>
    rw [comp_assoc]; rw [self_comp_symm]; rw [comp_refl]

@[simp]
/--
theorem `comp_right_inj` / 定理 `comp_right_inj`

English:
theorem comp_right_inj
  given: (h : M ≃[L] N) (f g : N ≃[L] P)
  statement: f.comp h = g.comp h ↔ f = g
  proof: ⟨fun eq => h.comp_right_injective eq, congr_arg (fun (r : N ≃[L] P) => r.comp h)⟩

中文:
定理 comp_right_inj
  条件: (h : M ≃[L] N) (f g : N ≃[L] P)
  结论: f.comp h = g.comp h ↔ f = g
  证明: ⟨fun eq => h.comp_right_injective eq, congr_arg (fun (r : N ≃[L] P) => r.comp h)⟩

Depends on / 依赖: comp_right_injective, congr_arg, h.comp_right_injective, r.comp
-/
theorem comp_right_inj (h : M ≃[L] N) (f g : N ≃[L] P) : f.comp h = g.comp h ↔ f = g :=
  ⟨fun eq => h.comp_right_injective eq, congr_arg (fun (r : N ≃[L] P) => r.comp h)⟩

end Equiv

/--
Definition of `StrongHomClass.toEquiv` / `StrongHomClass.toEquiv` 的定义

English:
definition StrongHomClass.toEquiv
  signature: {F M N} [L.Structure M] [L.Structure N] [EquivLike F M N]
  body: fun φ =>
  ⟨⟨φ, EquivLike.inv φ, EquivLike.left_inv φ, EquivLike.right_inv φ⟩, StrongHomClass.map_fun φ,
    StrongHomClass.map_rel φ⟩

中文:
定义 Strong态射类.toEquiv
  签名: {F M N} [L.结构 M] [L.结构 N] [等价状 F M N]
  定义体: fun φ =>
  ⟨⟨φ, EquivLike.inv φ, EquivLike.left_inv φ, EquivLike.right_inv φ⟩, StrongHomClass.map_fun φ,
    StrongHomClass.map_rel φ⟩
-/
@[simps] def StrongHomClass.toEquiv {F M N} [L.Structure M] [L.Structure N] [EquivLike F M N]
    [StrongHomClass L F M N] : F -> M ≃[L] N := fun φ =>
  ⟨⟨φ, EquivLike.inv φ, EquivLike.left_inv φ, EquivLike.right_inv φ⟩, StrongHomClass.map_fun φ,
    StrongHomClass.map_rel φ⟩

section SumStructure

variable (L₁ L₂ : Language) (S : Type*) [L₁.Structure S] [L₂.Structure S]

/--
Instance `sumStructure` / 实例 `sumStructure`

English:
instance sumStructure
  signature: : (L₁.sum L₂).Structure S where
  body: Sum.elim funMap funMap
  RelMap := Sum.elim RelMap RelMap

中文:
实例 sumStructure
  签名: : (L₁.求和 L₂).结构 S where
  定义体: Sum.elim funMap funMap
  RelMap := Sum.elim RelMap RelMap

Depends on / 依赖: Sum.elim, funMap, mem_lift_sets, monotone_principal, monotone_principal.comp
-/
instance sumStructure : (L₁.sum L₂).Structure S where
  funMap := Sum.elim funMap funMap
  RelMap := Sum.elim RelMap RelMap

variable {L₁ L₂ S}

@[simp]
/--
theorem `funMap_sumInl` / 定理 `funMap_sumInl`

English:
theorem funMap_sumInl
  given: {n : Nat} (f : L₁.Functions n)
  proof: rfl

@[simp]

中文:
定理 funMap_sumInl
  条件: {n : 自然数} (f : L₁.函数 n)
  证明: rfl

@[simp]
-/
theorem funMap_sumInl {n : Nat} (f : L₁.Functions n) :
    @funMap (L₁.sum L₂) S _ n (Sum.inl f) = funMap f :=
  rfl

@[simp]
/--
theorem `funMap_sumInr` / 定理 `funMap_sumInr`

English:
theorem funMap_sumInr
  given: {n : Nat} (f : L₂.Functions n)
  proof: rfl

@[simp]

中文:
定理 funMap_sumInr
  条件: {n : 自然数} (f : L₂.函数 n)
  证明: rfl

@[simp]
-/
theorem funMap_sumInr {n : Nat} (f : L₂.Functions n) :
    @funMap (L₁.sum L₂) S _ n (Sum.inr f) = funMap f :=
  rfl

@[simp]
/--
theorem `relMap_sumInl` / 定理 `relMap_sumInl`

English:
theorem relMap_sumInl
  given: {n : Nat} (R : L₁.Relations n)
  proof: rfl

@[simp]

中文:
定理 relMap_sumInl
  条件: {n : 自然数} (R : L₁.关系 n)
  证明: rfl

@[simp]

Depends on / 依赖: lift_le
-/
theorem relMap_sumInl {n : Nat} (R : L₁.Relations n) :
    @RelMap (L₁.sum L₂) S _ n (Sum.inl R) = RelMap R :=
  rfl

@[simp]
/--
theorem `relMap_sumInr` / 定理 `relMap_sumInr`

English:
theorem relMap_sumInr
  given: {n : Nat} (R : L₂.Relations n)
  proof: rfl

中文:
定理 relMap_sumInr
  条件: {n : 自然数} (R : L₂.关系 n)
  证明: rfl

Depends on / 依赖: lift_mono, principal_mono, principal_mono.mpr
-/
theorem relMap_sumInr {n : Nat} (R : L₂.Relations n) :
    @RelMap (L₁.sum L₂) S _ n (Sum.inr R) = RelMap R :=
  rfl


end SumStructure

section Empty

/-- Any type can be made uniquely into a structure over the empty language. -/
@[instance_reducible]
/--
Definition of `emptyStructure` / `emptyStructure` 的定义

English:
definition emptyStructure
  signature: : Language.empty.Structure M where

中文:
定义 emptyStructure
  签名: : Language.empty.结构 M where

Depends on / 依赖: principal_mono, principal_mono.mpr
-/
def emptyStructure : Language.empty.Structure M where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (Language.empty.Structure M)
  body: ⟨⟨Language.emptyStructure⟩, fun a => by
    ext _ f <;> exact Empty.elim f⟩

中文:
实例 :
  签名: 唯一 (Language.empty.结构 M)
  定义体: ⟨⟨Language.emptyStructure⟩, fun a => by
    ext _ f <;> exact Empty.elim f⟩

Depends on / 依赖: Empty.elim, Language, Language.emptyStructure, _mono, emptyStructure, le_antisymm, le_of_eq
-/
instance : Unique (Language.empty.Structure M) :=
  ⟨⟨Language.emptyStructure⟩, fun a => by
    ext _ f <;> exact Empty.elim f⟩

variable [Language.empty.Structure M] [Language.empty.Structure N]

instance (priority := 100) strongHomClassEmpty {F} [FunLike F M N] :
    StrongHomClass Language.empty F M N :=
  ⟨fun _ _ f => Empty.elim f, fun _ _ r => Empty.elim r⟩

@[simp]
/--
theorem `empty.nonempty_embedding_iff` / 定理 `empty.nonempty_embedding_iff`

English:
theorem empty.nonempty_embedding_iff
  proof: _root_.trans ⟨Nonempty.map fun f => f.toEmbedding, Nonempty.map StrongHomClass.toEmbedding⟩
    Cardinal.lift_mk_le'.symm

@[simp]

中文:
定理 empty.nonempty_embedding_iff
  证明: _root_.trans ⟨Nonempty.map fun f => f.toEmbedding, Nonempty.map StrongHomClass.toEmbedding⟩
    Cardinal.lift_mk_le'.symm

@[simp]

Depends on / 依赖: Cardinal, Cardinal.lift_mk_le, Nonempty, Nonempty.map, StrongHomClass, StrongHomClass.toEmbedding, _root_, _root_.trans, f.toEmbedding, lift_mk_le, toEmbedding
-/
theorem empty.nonempty_embedding_iff :
    Nonempty (M ↪[Language.empty] N) ↔ Cardinal.lift.{w'} #M <= Cardinal.lift.{w} #N :=
  _root_.trans ⟨Nonempty.map fun f => f.toEmbedding, Nonempty.map StrongHomClass.toEmbedding⟩
    Cardinal.lift_mk_le'.symm

@[simp]
/--
theorem `empty.nonempty_equiv_iff` / 定理 `empty.nonempty_equiv_iff`

English:
theorem empty.nonempty_equiv_iff
  proof: _root_.trans ⟨Nonempty.map fun f => f.toEquiv, Nonempty.map fun f => { toEquiv := f }⟩
    Cardinal.lift_mk_eq'.symm

中文:
定理 empty.nonempty_equiv_iff
  证明: _root_.trans ⟨Nonempty.map fun f => f.toEquiv, Nonempty.map fun f => { toEquiv := f }⟩
    Cardinal.lift_mk_eq'.symm

Depends on / 依赖: Cardinal, Cardinal.lift_mk_eq, Nonempty, Nonempty.map, _root_, _root_.trans, f.toEquiv, lift_map_le, lift_mk_eq, toEquiv
-/
theorem empty.nonempty_equiv_iff :
    Nonempty (M ≃[Language.empty] N) ↔ Cardinal.lift.{w'} #M = Cardinal.lift.{w} #N :=
  _root_.trans ⟨Nonempty.map fun f => f.toEquiv, Nonempty.map fun f => { toEquiv := f }⟩
    Cardinal.lift_mk_eq'.symm

/-- Makes a `Language.empty.Hom` out of any function.
This is only needed because there is no instance of `FunLike (M → N) M N`, and thus no instance of
`Language.empty.HomClass M N`. -/
@[simps]
/--
Definition of `_root_.Function.emptyHom` / `_root_.Function.emptyHom` 的定义

English:
definition _root_.Function.emptyHom
  signature: (f : M -> N)
  body: f

中文:
定义 _root_.函数.emptyHom
  签名: (f : M -> N)
  定义体: f

Depends on / 依赖: map_lift_eq2, monotone_principal, monotone_principal.comp
-/
def _root_.Function.emptyHom (f : M -> N) : M ->[Language.empty] N where toFun := f

end Empty

end Language

end FirstOrder

namespace Equiv

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

variable {L : Language} {M : Type*} {N : Type*} [L.Structure M]

/-- A structure induced by a bijection. -/
@[simps!, instance_reducible]
/--
Definition of `inducedStructure` / `inducedStructure` 的定义

English:
definition inducedStructure
  signature: (e : M ≃ N)
  body: ⟨fun f x => e (funMap f (e.symm ∘ x)), fun r x => RelMap r (e.symm ∘ x)⟩

中文:
定义 inducedStructure
  签名: (e : M ≃ N)
  定义体: ⟨fun f x => e (funMap f (e.symm ∘ x)), fun r x => RelMap r (e.symm ∘ x)⟩

Depends on / 依赖: RelMap, e.symm, funMap
-/
def inducedStructure (e : M ≃ N) : L.Structure N :=
  ⟨fun f x => e (funMap f (e.symm ∘ x)), fun r x => RelMap r (e.symm ∘ x)⟩

/--
Definition of `inducedStructureEquiv` / `inducedStructureEquiv` 的定义

English:
definition inducedStructureEquiv
  signature: (e : M ≃ N)
  body: by
  letI : L.Structure N := inducedStructure e
  exact
  { e with
    map_fun' := @fun n f x => by simp [← Function.comp_assoc e.symm e x]
    map_rel' := @fun n r x => by simp [← Function.comp_assoc e.symm e x] }

@[simp]

中文:
定义 inducedStructureEquiv
  签名: (e : M ≃ N)
  定义体: by
  letI : L.Structure N := inducedStructure e
  exact
  { e with
    map_fun' := @fun n f x => by simp [← Function.comp_assoc e.symm e x]
    map_rel' := @fun n r x => by simp [← Function.comp_assoc e.symm e x] }

@[simp]

Depends on / 依赖: Function, Function.comp_assoc, L.Structure, Structure, comap_lift_eq2, comp_assoc, e.symm, inducedStructure, map_fun, map_rel, monotone_principal, monotone_principal.comp
-/
def inducedStructureEquiv (e : M ≃ N) : @Language.Equiv L M N _ (inducedStructure e) := by
  letI : L.Structure N := inducedStructure e
  exact
  { e with
    map_fun' := @fun n f x => by simp [← Function.comp_assoc e.symm e x]
    map_rel' := @fun n r x => by simp [← Function.comp_assoc e.symm e x] }

@[simp]
/--
theorem `toEquiv_inducedStructureEquiv` / 定理 `toEquiv_inducedStructureEquiv`

English:
theorem toEquiv_inducedStructureEquiv
  given: (e : M ≃ N)
  proof: rfl

@[simp]

中文:
定理 toEquiv_inducedStructureEquiv
  条件: (e : M ≃ N)
  证明: rfl

@[simp]

Depends on / 依赖: lift_principal, monotone_principal, monotone_principal.comp
-/
theorem toEquiv_inducedStructureEquiv (e : M ≃ N) :
    @Language.Equiv.toEquiv L M N _ (inducedStructure e) (inducedStructureEquiv e) = e :=
  rfl

@[simp]
/--
theorem `toFun_inducedStructureEquiv` / 定理 `toFun_inducedStructureEquiv`

English:
theorem toFun_inducedStructureEquiv
  given: (e : M ≃ N)
  proof: rfl

@[simp]

中文:
定理 toFun_inducedStructureEquiv
  条件: (e : M ≃ N)
  证明: rfl

@[simp]

Depends on / 依赖: _principal, principal_singleton
-/
theorem toFun_inducedStructureEquiv (e : M ≃ N) :
    DFunLike.coe (@inducedStructureEquiv L M N _ e) = e :=
  rfl

@[simp]
/--
theorem `toFun_inducedStructureEquiv_Symm` / 定理 `toFun_inducedStructureEquiv_Symm`

English:
theorem toFun_inducedStructureEquiv_Symm
  given: (e : M ≃ N)
  proof: rfl

中文:
定理 toFun_inducedStructureEquiv_Symm
  条件: (e : M ≃ N)
  证明: rfl

Depends on / 依赖: _principal, inducedStructure, principal_empty
-/
theorem toFun_inducedStructureEquiv_Symm (e : M ≃ N) :
    (by
    letI : L.Structure N := inducedStructure e
    exact DFunLike.coe (@inducedStructureEquiv L M N _ e).symm) = (e.symm : N -> M) :=
  rfl

end Equiv
