/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Data.Set.Subsingleton

/-!
# A simplified basis for partial recursive functions

This file defines `Nat.Partrec'`, an inductive predicate that provides an
alternative, structural basis for partial recursive functions using vectors.
It establishes the equivalence between this vector-based definition and the
standard `Partrec` definition.
-/

@[expose] public section

open List (Vector)
open Encodable Denumerable

namespace Nat

open Vector Part

/--
Inductive type `Partrec'` / 归纳类型 `Partrec'`

English:
inductive Partrec'
  parameters: : forall {n}, (List.Vector Nat n ->. Nat) -> Prop
  constructors (3):
    - prim: {n f} : @Primrec' n f -> @Partrec' n f
    - comp: {m n f} (g : Fin n -> List.Vector Nat m ->. Nat) : Partrec' f -> (forall i, Partrec' (g i)) -> Partrec' fun v => (List.Vector.mOfFn fun i => g i v) >>= f
    - rfind: {n} {f : List.Vector Nat (n + 1) -> Nat} : @Partrec' (n + 1) f -> Partrec' fun v => rfind fun n => some (f (n ::ᵥ v) = 0)

中文:
归纳类型 Partrec'
  参数: : 对任意 {n}, (列表.Vector 自然数 n ->. 自然数) -> 命题
  构造子 (3 个):
    - prim: {n f} : @Primrec' n f -> @Partrec' n f
    - comp: {m n f} (g : 有限集 n -> 列表.Vector 自然数 m ->. 自然数) : Partrec' f -> (对任意 i, Partrec' (g i)) -> Partrec' fun v => (列表.Vector.mOfFn fun i => g i v) >>= f
    - rfind: {n} {f : 列表.Vector 自然数 (n + 1) -> 自然数} : @Partrec' (n + 1) f -> Partrec' fun v => rfind fun n => some (f (n ::ᵥ v) = 0)
-/
inductive Partrec' : forall {n}, (List.Vector Nat n ->. Nat) -> Prop
  | prim {n f} : @Primrec' n f -> @Partrec' n f
  | comp {m n f} (g : Fin n -> List.Vector Nat m ->. Nat) :
    Partrec' f -> (forall i, Partrec' (g i)) ->
      Partrec' fun v => (List.Vector.mOfFn fun i => g i v) >>= f
  | rfind {n} {f : List.Vector Nat (n + 1) -> Nat} :
    @Partrec' (n + 1) f -> Partrec' fun v => rfind fun n => some (f (n ::ᵥ v) = 0)

end Nat

namespace Nat.Partrec'

open List.Vector Computable

open Nat.Partrec'

/--
theorem `to_part` / 定理 `to_part`

English:
theorem to_part
  given: {n f} (pf : @Partrec' n f)
  statement: Partrec f
  proof: by
  induction pf with
  | prim hf => exact hf.to_prim.to_comp
  | comp _ _ _ hf hg => exact (Partrec.vector_mOfFn hg).bind (hf.comp snd)
  | rfind _ hf =>
    have := hf.comp (vector_cons.comp snd fst)
    have :=
      ((Primrec.eq.decide.comp _root_.Primrec.id (_root_.Primrec.const 0)).to_comp.co

中文:
定理 to_part
  条件: {n f} (pf : @Partrec' n f)
  结论: Partrec f
  证明: by
  induction pf with
  | prim hf => exact hf.to_prim.to_comp
  | comp _ _ _ hf hg => exact (Partrec.vector_mOfFn hg).bind (hf.comp snd)
  | rfind _ hf =>
    have := hf.comp (vector_cons.comp snd fst)
    have :=
      ((Primrec.eq.decide.comp _root_.Primrec.id (_root_.Primrec.const 0)).to_comp.co

Depends on / 依赖: Partrec, Partrec.vector_mOfFn, Primrec, Primrec.eq.decide.comp, _root_, _root_.Partrec.rfind, _root_.Primrec.const, _root_.Primrec.id, hf.comp, hf.to_prim.to_comp, to_comp, to_comp.comp, to_prim, vector_cons, vector_cons.comp, vector_mOfFn
-/
theorem to_part {n f} (pf : @Partrec' n f) : Partrec f := by
  induction pf with
  | prim hf => exact hf.to_prim.to_comp
  | comp _ _ _ hf hg => exact (Partrec.vector_mOfFn hg).bind (hf.comp snd)
  | rfind _ hf =>
    have := hf.comp (vector_cons.comp snd fst)
    have :=
      ((Primrec.eq.decide.comp _root_.Primrec.id (_root_.Primrec.const 0)).to_comp.comp
        this).to₂.partrec₂
    exact _root_.Partrec.rfind this

/--
theorem `of_eq` / 定理 `of_eq`

English:
theorem of_eq
  given: {n} {f g : List.Vector Nat n ->. Nat} (hf : Partrec' f) (H : forall i, f i = g i)
  proof: (funext H : f = g) ▸ hf

中文:
定理 of_eq
  条件: {n} {f g : 列表.Vector 自然数 n ->. 自然数} (hf : Partrec' f) (H : 对任意 i, f i = g i)
  证明: (funext H : f = g) ▸ hf
-/
theorem of_eq {n} {f g : List.Vector Nat n ->. Nat} (hf : Partrec' f) (H : forall i, f i = g i) :
    Partrec' g :=
  (funext H : f = g) ▸ hf

/--
theorem `of_prim` / 定理 `of_prim`

English:
theorem of_prim
  given: {n} {f : List.Vector Nat n -> Nat} (hf : Primrec f)
  statement: @Partrec' n f
  proof: prim (Nat.Primrec'.of_prim hf)

中文:
定理 of_prim
  条件: {n} {f : 列表.Vector 自然数 n -> 自然数} (hf : Primrec f)
  结论: @Partrec' n f
  证明: prim (Nat.Primrec'.of_prim hf)

Depends on / 依赖: Nat.Primrec, Primrec, of_prim
-/
theorem of_prim {n} {f : List.Vector Nat n -> Nat} (hf : Primrec f) : @Partrec' n f :=
  prim (Nat.Primrec'.of_prim hf)

/--
theorem `head` / 定理 `head`

English:
theorem head
  given: {n : Nat}
  statement: @Partrec' n.succ (@head Nat n)
  proof: prim Nat.Primrec'.head

中文:
定理 head
  条件: {n : 自然数}
  结论: @Partrec' n.succ (@head 自然数 n)
  证明: prim Nat.Primrec'.head

Depends on / 依赖: Nat.Primrec, Primrec
-/
theorem head {n : Nat} : @Partrec' n.succ (@head Nat n) :=
  prim Nat.Primrec'.head

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `tail` / 定理 `tail`

English:
theorem tail
  given: {n f} (hf : @Partrec' n f)
  statement: @Partrec' n.succ fun v => f v.tail
  proof: (hf.comp _ fun i => @prim _ _ <| Nat.Primrec'.get i.succ).of_eq fun v => by
    rw [← ofFn_get v.tail]; rw [funext (get_tail_succ v)]
    simp

中文:
定理 tail
  条件: {n f} (hf : @Partrec' n f)
  结论: @Partrec' n.succ fun v => f v.tail
  证明: (hf.comp _ fun i => @prim _ _ <| Nat.Primrec'.get i.succ).of_eq fun v => by
    rw [← ofFn_get v.tail]; rw [funext (get_tail_succ v)]
    simp

Depends on / 依赖: Nat.Primrec, Primrec, get_tail_succ, hf.comp, i.succ, ofFn_get, of_eq, v.tail
-/
theorem tail {n f} (hf : @Partrec' n f) : @Partrec' n.succ fun v => f v.tail :=
  (hf.comp _ fun i => @prim _ _ <| Nat.Primrec'.get i.succ).of_eq fun v => by
    rw [← ofFn_get v.tail]; rw [funext (get_tail_succ v)]
    simp

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `bind` / 定理 `bind`

English:
theorem bind
  given: {n f g} (hf : @Partrec' n f) (hg : @Partrec' (n + 1) g)
  proof: (@comp n (n + 1) g (Fin.cases f (fun i v => some (v.get i))) hg <|
      Fin.cases (by simpa using! hf) (fun i => by simpa using! prim (Nat.Primrec'.get i))).of_eq
    fun v => by simp [mOfFn, Part.bind_assoc, pure]

中文:
定理 bind
  条件: {n f g} (hf : @Partrec' n f) (hg : @Partrec' (n + 1) g)
  证明: (@comp n (n + 1) g (Fin.cases f (fun i v => some (v.get i))) hg <|
      Fin.cases (by simpa using! hf) (fun i => by simpa using! prim (Nat.Primrec'.get i))).of_eq
    fun v => by simp [mOfFn, Part.bind_assoc, pure]
-/
protected theorem bind {n f g} (hf : @Partrec' n f) (hg : @Partrec' (n + 1) g) :
    @Partrec' n fun v => (f v).bind fun a => g (a ::ᵥ v) :=
  (@comp n (n + 1) g (Fin.cases f (fun i v => some (v.get i))) hg <|
      Fin.cases (by simpa using! hf) (fun i => by simpa using! prim (Nat.Primrec'.get i))).of_eq
    fun v => by simp [mOfFn, Part.bind_assoc, pure]

/--
theorem `map` / 定理 `map`

English:
theorem map
  statement: {n f} {g : List.Vector Nat (n + 1) -> Nat} (hf : @Partrec' n f)
  proof: by
  simpa [(Part.bind_some_eq_map _ _).symm] using hf.bind hg

中文:
定理 map
  结论: {n f} {g : 列表.Vector 自然数 (n + 1) -> 自然数} (hf : @Partrec' n f)
  证明: by
  simpa [(Part.bind_some_eq_map _ _).symm] using hf.bind hg
-/
protected theorem map {n f} {g : List.Vector Nat (n + 1) -> Nat} (hf : @Partrec' n f)
    (hg : @Partrec' (n + 1) g) : @Partrec' n fun v => (f v).map fun a => g (a ::ᵥ v) := by
  simpa [(Part.bind_some_eq_map _ _).symm] using hf.bind hg

/--
Definition of `Vec` / `Vec` 的定义

English:
definition Vec
  signature: {n m} (f : List.Vector Nat n -> List.Vector Nat m)
  body: forall i, Partrec' fun v => (f v).get i

nonrec theorem Vec.prim {n m f} (hf : @Nat.Primrec'.Vec n m f) : Vec f := fun i => prim hf i

中文:
定义 Vec
  签名: {n m} (f : 列表.Vector 自然数 n -> 列表.Vector 自然数 m)
  定义体: forall i, Partrec' fun v => (f v).get i

nonrec theorem Vec.prim {n m f} (hf : @Nat.Primrec'.Vec n m f) : Vec f := fun i => prim hf i

Depends on / 依赖: Partrec
-/
def Vec {n m} (f : List.Vector Nat n -> List.Vector Nat m) :=
  forall i, Partrec' fun v => (f v).get i

nonrec theorem Vec.prim {n m f} (hf : @Nat.Primrec'.Vec n m f) : Vec f := fun i => prim hf i

/--
theorem `nil` / 定理 `nil`

English:
theorem nil
  given: {n}
  statement: @Vec n 0 fun _ => nil
  proof: fun i => i.elim0

中文:
定理 nil
  条件: {n}
  结论: @Vec n 0 fun _ => nil
  证明: fun i => i.elim0
-/
protected theorem nil {n} : @Vec n 0 fun _ => nil := fun i => i.elim0

/--
theorem `cons` / 定理 `cons`

English:
theorem cons
  statement: {n m} {f : List.Vector Nat n -> Nat} {g} (hf : @Partrec' n f)
  proof: fun i =>
  Fin.cases (by simpa using! hf) (fun i => by simp only [hg i, get_cons_succ]) i

中文:
定理 cons
  结论: {n m} {f : 列表.Vector 自然数 n -> 自然数} {g} (hf : @Partrec' n f)
  证明: fun i =>
  Fin.cases (by simpa using! hf) (fun i => by simp only [hg i, get_cons_succ]) i
-/
protected theorem cons {n m} {f : List.Vector Nat n -> Nat} {g} (hf : @Partrec' n f)
    (hg : @Vec n m g) : Vec fun v => f v ::ᵥ g v := fun i =>
  Fin.cases (by simpa using! hf) (fun i => by simp only [hg i, get_cons_succ]) i

/--
theorem `idv` / 定理 `idv`

English:
theorem idv
  given: {n}
  statement: @Vec n n id
  proof: Vec.prim Nat.Primrec'.idv

中文:
定理 idv
  条件: {n}
  结论: @Vec n n id
  证明: Vec.prim Nat.Primrec'.idv

Depends on / 依赖: Nat.Primrec, Primrec, Vec.prim
-/
theorem idv {n} : @Vec n n id :=
  Vec.prim Nat.Primrec'.idv

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `comp'` / 定理 `comp'`

English:
theorem comp'
  given: {n m f g} (hf : @Partrec' m f) (hg : @Vec n m g)
  statement: Partrec' fun v => f (g v)
  proof: (hf.comp _ hg).of_eq fun v => by simp

中文:
定理 comp'
  条件: {n m f g} (hf : @Partrec' m f) (hg : @Vec n m g)
  结论: Partrec' fun v => f (g v)
  证明: (hf.comp _ hg).of_eq fun v => by simp

Depends on / 依赖: hf.comp, lex_iff_of_unique, of_eq
-/
theorem comp' {n m f g} (hf : @Partrec' m f) (hg : @Vec n m g) : Partrec' fun v => f (g v) :=
  (hf.comp _ hg).of_eq fun v => by simp

/--
theorem `comp₁` / 定理 `comp₁`

English:
theorem comp₁
  statement: {n} (f : Nat ->. Nat) {g : List.Vector Nat n -> Nat} (hf : @Partrec' 1 fun v => f v.head)
  proof: by
  simpa using hf.comp' (Partrec'.cons hg Partrec'.nil)

中文:
定理 comp₁
  结论: {n} (f : 自然数 ->. 自然数) {g : 列表.Vector 自然数 n -> 自然数} (hf : @Partrec' 1 fun v => f v.head)
  证明: by
  simpa using hf.comp' (Partrec'.cons hg Partrec'.nil)

Depends on / 依赖: Partrec, hf.comp
-/
theorem comp₁ {n} (f : Nat ->. Nat) {g : List.Vector Nat n -> Nat} (hf : @Partrec' 1 fun v => f v.head)
    (hg : @Partrec' n g) : @Partrec' n fun v => f (g v) := by
  simpa using hf.comp' (Partrec'.cons hg Partrec'.nil)

/--
theorem `rfindOpt` / 定理 `rfindOpt`

English:
theorem rfindOpt
  given: {n} {f : List.Vector Nat (n + 1) -> Nat} (hf : @Partrec' (n + 1) f)
  proof: ((rfind <|
        (of_prim (Primrec.nat_sub.comp (_root_.Primrec.const 1) Primrec.vector_head)).comp₁
          (fun n => Part.some (1 - n)) hf).bind
    ((prim Nat.Primrec'.pred).comp₁ Nat.pred hf)).of_eq
    fun v =>
    Part.ext fun b => by
      simp only [Nat.rfindOpt, Nat.sub_eq_zero_iff_le, 

中文:
定理 rfindOpt
  条件: {n} {f : 列表.Vector 自然数 (n + 1) -> 自然数} (hf : @Partrec' (n + 1) f)
  证明: ((rfind <|
        (of_prim (Primrec.nat_sub.comp (_root_.Primrec.const 1) Primrec.vector_head)).comp₁
          (fun n => Part.some (1 - n)) hf).bind
    ((prim Nat.Primrec'.pred).comp₁ Nat.pred hf)).of_eq
    fun v =>
    Part.ext fun b => by
      simp only [Nat.rfindOpt, Nat.sub_eq_zero_iff_le, 

Depends on / 依赖: Iff.rfl, Nat.Primrec, Nat.pred, Nat.rfindOpt, Nat.sub_eq_zero_iff_le, Option.mem_def, PFun.coe_val, Part.ext, Part.mem_bind_iff, Part.mem_coe, Part.mem_some_iff, Part.some, Primrec, Primrec.nat_sub.comp, Primrec.vector_head, _root_, _root_.Primrec.const, and_congr, and_congr_right, coe_val
-/
theorem rfindOpt {n} {f : List.Vector Nat (n + 1) -> Nat} (hf : @Partrec' (n + 1) f) :
    @Partrec' n fun v => Nat.rfindOpt fun a => ofNat (Option Nat) (f (a ::ᵥ v)) :=
  ((rfind <|
        (of_prim (Primrec.nat_sub.comp (_root_.Primrec.const 1) Primrec.vector_head)).comp₁
          (fun n => Part.some (1 - n)) hf).bind
    ((prim Nat.Primrec'.pred).comp₁ Nat.pred hf)).of_eq
    fun v =>
    Part.ext fun b => by
      simp only [Nat.rfindOpt, Nat.sub_eq_zero_iff_le, PFun.coe_val, Part.mem_bind_iff,
        Part.mem_some_iff, Option.mem_def, Part.mem_coe]
      refine
        exists_congr fun a => (and_congr (iff_of_eq ?_) Iff.rfl).trans (and_congr_right fun h => ?_)
      · congr
        funext n
        cases f (n ::ᵥ v) <;> simp <;> rfl
      · have := Nat.rfind_spec h
        simp only [Part.coe_some, Part.mem_some_iff] at this
        revert this; rcases f (a ::ᵥ v) with - | c <;> intro this
        · cases this
        rw [← Option.some_inj]; rw [eq_comm]
        rfl

open Nat.Partrec.Code

/--
theorem `of_part` / 定理 `of_part`

English:
theorem of_part
  statement: forall {n f}, Partrec f -> @Partrec' n f
  proof: @(suffices forall f, Nat.Partrec f -> @Partrec' 1 fun v => f v.head from fun {n f} hf => by
      let g := fun n₁ =>
        (Part.ofOption (decode (α := List.Vector Nat n) n₁)).bind (fun a => Part.map encode (f a))
      exact
        (comp₁ g (this g hf) (prim Nat.Primrec'.encode)).of_eq fun i => 

中文:
定理 of_part
  结论: 对任意 {n f}, Partrec f -> @Partrec' n f
  证明: @(suffices forall f, Nat.Partrec f -> @Partrec' 1 fun v => f v.head from fun {n f} hf => by
      let g := fun n₁ =>
        (Part.ofOption (decode (α := List.Vector Nat n) n₁)).bind (fun a => Part.map encode (f a))
      exact
        (comp₁ g (this g hf) (prim Nat.Primrec'.encode)).of_eq fun i => 

Depends on / 依赖: Lex.isStrictOrder, List.Vector, Nat.Partrec, Nat.Primrec, Part.map, Part.map_id, Part.ofOption, Partrec, Primrec, Primrec.encode_iff, Primrec.vector_head.pair, Vector, _root_, _root_.Primrec, decode, encode, encode_iff, encodek, eval_eq_rfindOpt, exists_code
-/
theorem of_part : forall {n f}, Partrec f -> @Partrec' n f :=
  @(suffices forall f, Nat.Partrec f -> @Partrec' 1 fun v => f v.head from fun {n f} hf => by
      let g := fun n₁ =>
        (Part.ofOption (decode (α := List.Vector Nat n) n₁)).bind (fun a => Part.map encode (f a))
      exact
        (comp₁ g (this g hf) (prim Nat.Primrec'.encode)).of_eq fun i => by
          dsimp only [g]; simp [encodek, Part.map_id']
    fun f hf => by
    obtain ⟨c, rfl⟩ := exists_code.1 hf
    simpa [eval_eq_rfindOpt] using
rfindOpt
of_prim
Primrec.encode_iff.2
primrec_evaln.comp
(Primrec.vector_head.pair (_root_.Primrec.const c)).pair
                Primrec.vector_head.comp Primrec.vector_tail)

/--
theorem `part_iff` / 定理 `part_iff`

English:
theorem part_iff
  given: {n f}
  statement: @Partrec' n f ↔ Partrec f
  proof: ⟨to_part, of_part⟩

中文:
定理 part_iff
  条件: {n f}
  结论: @Partrec' n f ↔ Partrec f
  证明: ⟨to_part, of_part⟩

Depends on / 依赖: of_part, to_part
-/
theorem part_iff {n f} : @Partrec' n f ↔ Partrec f :=
  ⟨to_part, of_part⟩

/--
theorem `part_iff₁` / 定理 `part_iff₁`

English:
theorem part_iff₁
  given: {f : Nat ->. Nat}
  statement: (@Partrec' 1 fun v => f v.head) ↔ Partrec f
  proof: part_iff.trans
    ⟨fun h =>
      (h.comp <| (Primrec.vector_ofFn fun _ => _root_.Primrec.id).to_comp).of_eq fun v => by
        simp only [id, head_ofFn],
      fun h => h.comp vector_head⟩

中文:
定理 part_iff₁
  条件: {f : 自然数 ->. 自然数}
  结论: (@Partrec' 1 fun v => f v.head) ↔ Partrec f
  证明: part_iff.trans
    ⟨fun h =>
      (h.comp <| (Primrec.vector_ofFn fun _ => _root_.Primrec.id).to_comp).of_eq fun v => by
        simp only [id, head_ofFn],
      fun h => h.comp vector_head⟩

Depends on / 依赖: Primrec, Primrec.vector_ofFn, _root_, _root_.Primrec.id, h.comp, head_ofFn, of_eq, part_iff, part_iff.trans, to_comp, vector_head, vector_ofFn
-/
theorem part_iff₁ {f : Nat ->. Nat} : (@Partrec' 1 fun v => f v.head) ↔ Partrec f :=
  part_iff.trans
    ⟨fun h =>
      (h.comp <| (Primrec.vector_ofFn fun _ => _root_.Primrec.id).to_comp).of_eq fun v => by
        simp only [id, head_ofFn],
      fun h => h.comp vector_head⟩

/--
theorem `part_iff₂` / 定理 `part_iff₂`

English:
theorem part_iff₂
  given: {f : Nat -> Nat ->. Nat}
  statement: (@Partrec' 2 fun v => f v.head v.tail.head) ↔ Partrec₂ f
  proof: part_iff.trans
    ⟨fun h =>
      (h.comp <| vector_cons.comp fst <| vector_cons.comp snd (const nil)).of_eq fun v => by
        simp only [head_cons, tail_cons],
      fun h => h.comp vector_head (vector_head.comp vector_tail)⟩

中文:
定理 part_iff₂
  条件: {f : 自然数 -> 自然数 ->. 自然数}
  结论: (@Partrec' 2 fun v => f v.head v.tail.head) ↔ Partrec₂ f
  证明: part_iff.trans
    ⟨fun h =>
      (h.comp <| vector_cons.comp fst <| vector_cons.comp snd (const nil)).of_eq fun v => by
        simp only [head_cons, tail_cons],
      fun h => h.comp vector_head (vector_head.comp vector_tail)⟩

Depends on / 依赖: Lex.partialOrder, h.comp, head_cons, of_eq, part_iff, part_iff.trans, partialOrder, tail_cons, vector_cons, vector_cons.comp, vector_head, vector_head.comp, vector_tail
-/
theorem part_iff₂ {f : Nat -> Nat ->. Nat} : (@Partrec' 2 fun v => f v.head v.tail.head) ↔ Partrec₂ f :=
  part_iff.trans
    ⟨fun h =>
      (h.comp <| vector_cons.comp fst <| vector_cons.comp snd (const nil)).of_eq fun v => by
        simp only [head_cons, tail_cons],
      fun h => h.comp vector_head (vector_head.comp vector_tail)⟩

/--
theorem `vec_iff` / 定理 `vec_iff`

English:
theorem vec_iff
  given: {m n f}
  statement: @Vec m n f ↔ Computable f
  proof: ⟨fun h => by simpa only [ofFn_get] using vector_ofFn fun i => to_part (h i), fun h i =>
of_part vector_get.comp h (const i)⟩

中文:
定理 vec_iff
  条件: {m n f}
  结论: @Vec m n f ↔ 可计算 f
  证明: ⟨fun h => by simpa only [ofFn_get] using vector_ofFn fun i => to_part (h i), fun h i =>
of_part vector_get.comp h (const i)⟩

Depends on / 依赖: ofFn_get, of_part, to_part, vector_get, vector_get.comp, vector_ofFn
-/
theorem vec_iff {m n f} : @Vec m n f ↔ Computable f :=
  ⟨fun h => by simpa only [ofFn_get] using vector_ofFn fun i => to_part (h i), fun h i =>
of_part vector_get.comp h (const i)⟩

end Nat.Partrec'
